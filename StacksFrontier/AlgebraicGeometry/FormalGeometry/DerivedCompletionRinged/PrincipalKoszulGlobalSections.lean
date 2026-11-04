module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.UnboundedGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalKoszulTowerDerivedSections
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The two-term Koszul projection formula for derived global sections on a ringed site

Let `(𝒞, 𝒪)` be a ringed site, let `ρ : A ⟶ Γ(𝒞, 𝒪)` be a homomorphism from a commutative ring
`A` and let `f ∈ A`.  Multiplication by the global section `ρ f` of `𝒪` is a central endomorphism
of `Mod(𝒪)`, so every cochain complex `E` of sheaves of `𝒪`-modules carries the tower of cones of
its powers, a model for the `f`-power Koszul tower `n ↦ E ⊗_𝒪 (𝒪 --f^(n+1)--> 𝒪)`.  This file
proves that `A`-linear derived global sections carry that tower to the `f`-power Koszul tower of
`RΓ(𝒞, E)` over `A`:

`RΓ(𝒞, E ⊗_𝒪 (𝒪 --f^(n+1)--> 𝒪)) ≅ RΓ(𝒞, E) ⊗^𝐋_A (A --f^(n+1)--> A)`,

as an isomorphism of inverse systems `ℕᵒᵖ ⥤ D(A)`.

## Main definitions

* `CochainComplex.koszulConeTower`: the tower of cones of the powers of multiplication by a
  scalar, in a category linear over a commutative ring.  This is
  `PrincipalTorsionTower.principalComplexSystem` read in an arbitrary linear category, which is
  what lets one and the same tower be formed on the sheaves of `𝒪`-modules and on the
  `A`-modules.
* `CochainComplex.koszulConeTowerMap`: the map of towers induced by a map of complexes.
* `CochainComplex.koszulConeTowerSemilinearIso`: the comparison of towers along an additive
  functor carrying multiplication by one scalar to multiplication by another.
* `AlgebraicGeometry.RingedSite.sectionsRingHom` and
  `AlgebraicGeometry.RingedSite.linearBaseRingSheaf`: multiplication by a global section of `𝒪`,
  as a ring map into the centre of the category of sheaves of `𝒪`-modules, and the resulting
  `A`-linear structure on that category.

## Main results

* `AlgebraicGeometry.RingedSite.map_smul_id_moduleGlobalSectionsOver`: **`A`-linear global
  sections are `A`-linear** — they carry multiplication by the image of `a` in `Γ(𝒞, 𝒪)` to
  multiplication by `a`.  This is the naturality of multiplication by a global section, read
  against the description of the `A`-action on `Γ(𝒞, ℱ) = Hom_𝒪(𝒪, ℱ)` as precomposition.
* `AlgebraicGeometry.RingedSite.nonempty_iso_koszulConeTower_derivedGlobalSections`: the
  projection formula above, as an isomorphism of inverse systems in `D(A)`, for an arbitrary
  ringed site and an arbitrary cochain complex of sheaves of `𝒪`-modules.  Nothing is assumed:
  no quasi-coherence, no finiteness and no nilpotence.

## Implementation notes

The tower is formed with cones rather than with a derived tensor product because the two-term
complex `𝒪 --f^(n+1)--> 𝒪` is a complex of free modules of rank one, so no K-flat resolution
intervenes.  That is the same choice `PrincipalTorsionTower.principalComplexSystem` makes on the
module side, and the two towers are then literally the same construction in two linear
categories, which is why the generic section below exists: the module-side definition is an
abbreviation with a large number of consumers, so it is generalized by a statement of the same
construction over an arbitrary linear category rather than in place, and
`CochainComplex.principalComplexSystem_eq_koszulConeTower` records that they agree.

The proof is the one of `Stacks.Cohomology.KoszulTowerSections`
`.nonempty_iso_koszulTower_derivedSections`, which is this statement for a ringed *space* and the
sections over the base ring of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/DerivedSectionsOverBase.lean`.
Four steps: replace `E` by a K-injective resolution `J`, whose
Koszul tower has K-injective terms because a cone of a morphism of K-injective complexes is
K-injective; compute `RΓ` of each of those terms by termwise global sections, the comparison of
`Stacks.Injectives.complexUnit` being invertible there; carry the tower of cones through termwise
global sections, which is the generic comparison applied to
`map_smul_id_moduleGlobalSectionsOver`; and compare the representative `Γ(𝒞, J)` of `RΓ(𝒞, E)`
with the one the module-side tower is built on, through a K-injective resolution over `A`.

The `A`-linear structure on `Mod(𝒪)` is the one `Stacks.SheafOfModules.linearOfTerminalSection`
has for a section over a terminal object, built here out of a compatible family of local sections
instead, which is what a site with no terminal object leaves available.  It is a `def` and not an
instance, the ring `A` and the map `ρ` not being determined by the site, so it is introduced with
`letI` at the point of use, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BaseRingLinear.lean`.  Writing the scalars as `A`
rather than as the centre of `Mod(𝒪)` is deliberate: a scalar of type `CatCenter (Mod 𝒪)` makes
`•` resolve through that type's own action and not through the linear structure, and the two are
equal only up to `CategoryTheory.CatCenter.smul_eq'`.  The generic comparison of towers is
nevertheless stated for a pair of scalars in two different rings, which costs nothing and is the
shape an additive functor between categories linear over different rings presents.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Preadditive CategoryTheory.Linear
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace CochainComplex

/-- Multiplication by `r ^ (k + 1)` factors as multiplication by `r` followed by multiplication
by `r ^ k`. -/
private theorem pow_succ_smul_id {R : Type*} [CommRing R] {𝒜 : Type*} [Category* 𝒜]
    [Preadditive 𝒜] [Linear R 𝒜] (r : R) (k : ℕ) (M : 𝒜) :
    r ^ (k + 1) • 𝟙 M = (r • 𝟙 M) ≫ (r ^ k • 𝟙 M) := by
  simp [comp_smul, smul_smul, pow_succ', mul_comm]

/-! ### The Koszul tower of cones in a linear category -/

section Tower

variable {R : Type*} [CommRing R] {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜] [Linear R 𝒜]
  [HasBinaryBiproducts 𝒜]

/-- **The `f`-power Koszul tower of a cochain complex in an `R`-linear category**: the tower of
cones of multiplication by `f ^ (n + 1)`, with transition maps induced by multiplication by `f`
on the source of the cone and the identity on its target. -/
abbrev koszulConeTower (f : R) (C : CochainComplex 𝒜 ℤ) : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ :=
  Functor.ofOpSequence (X := fun n ↦ mappingCone (f ^ (n + 1) • 𝟙 C))
    (fun n ↦ mappingCone.map _ _ (f • 𝟙 C) (𝟙 C) (by
      simp [comp_smul, smul_smul, pow_succ', mul_comm]))

/-- **A map of complexes induces a map of `f`-power Koszul towers**: on the `n`-th term it is the
cone map of the square expressing that the map commutes with multiplication by `f ^ (n + 1)`. -/
def koszulConeTowerMap (f : R) {C D : CochainComplex 𝒜 ℤ} (g : C ⟶ D) :
    koszulConeTower f C ⟶ koszulConeTower f D :=
  NatTrans.ofOpSequence
    (fun n ↦ mappingCone.map _ _ g g (by simp [smul_comp, comp_smul])) (by
    intro n
    simp only [koszulConeTower, Functor.ofOpSequence_map_homOfLE_succ]
    exact mappingCone.map_comp_map_eq _ _ _ _ _ _ _ _
      (by simp [smul_comp, comp_smul]) (by simp))

end Tower

/-- The `f`-power Koszul tower of a complex of `A`-modules is the tower of cones in the
`A`-linear category of `A`-modules: the two constructions are the same. -/
theorem principalComplexSystem_eq_koszulConeTower {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) :
    PrincipalTorsionTower.principalComplexSystem A f C = koszulConeTower f C := rfl

section Devissage

attribute [local instance] HasDerivedCategory.standard

variable {R : Type*} [CommRing R] {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [Linear R 𝒜]

/-- If a map of complexes is invertible in the derived category then the induced map of
`f`-power Koszul towers is invertible levelwise: both cone triangles have invertible first two
maps. -/
instance isIso_whiskerRight_koszulConeTowerMap (f : R) {C D : CochainComplex 𝒜 ℤ} (g : C ⟶ D)
    [IsIso (DerivedCategory.Q.map g)] :
    IsIso (Functor.whiskerRight (koszulConeTowerMap f g) DerivedCategory.Q) := by
  have hi (n : ℕᵒᵖ) :
      IsIso ((Functor.whiskerRight (koszulConeTowerMap f g) DerivedCategory.Q).app n) := by
    refine isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map
        (mappingCone.triangleMap
          (f ^ (n.unop + 1) • 𝟙 C) (f ^ (n.unop + 1) • 𝟙 D) g g (by simp [smul_comp, comp_smul])))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) ?_ ?_
    · change IsIso (DerivedCategory.Q.map g); infer_instance
    · change IsIso (DerivedCategory.Q.map g); infer_instance
  exact NatIso.isIso_of_isIso_app _

end Devissage

/-! ### An additive functor carries one Koszul tower to the other -/

section Semilinear

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]
  {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜] [Linear R 𝒜] [HasBinaryBiproducts 𝒜]
  {ℬ : Type*} [Category* ℬ] [Preadditive ℬ] [Linear S ℬ] [HasBinaryBiproducts ℬ]
  (H : 𝒜 ⥤ ℬ) [H.Additive] {r : R} {s : S}
  (hrs : ∀ M : 𝒜, H.map (r • 𝟙 M) = s • 𝟙 (H.obj M))

include hrs

/-- A functor carrying multiplication by `r` to multiplication by `s` carries the powers of the
one to the powers of the other. -/
theorem map_pow_smul_id (k : ℕ) (M : 𝒜) : H.map (r ^ k • 𝟙 M) = s ^ k • 𝟙 (H.obj M) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ_smul_id r k M, H.map_comp, ih, hrs, pow_succ_smul_id s k]

/-- Termwise application of the functor carries multiplication by `r` on a complex to
multiplication by `s`. -/
theorem mapHomologicalComplex_map_smul_id (C : CochainComplex 𝒜 ℤ) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (r • 𝟙 C) =
      s • 𝟙 ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  HomologicalComplex.hom_ext _ _ fun i ↦ hrs (C.X i)

/-- Termwise application of the functor carries the powers of multiplication by `r` on a complex
to the powers of multiplication by `s`. -/
theorem mapHomologicalComplex_map_pow_smul_id (k : ℕ) (C : CochainComplex 𝒜 ℤ) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (r ^ k • 𝟙 C) =
      s ^ k • 𝟙 ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  HomologicalComplex.hom_ext _ _ fun i ↦ map_pow_smul_id H hrs k (C.X i)

/-- The levelwise comparison of `koszulConeTowerSemilinearIso`: the image of the cone of
multiplication by `r ^ (n + 1)` is the cone of multiplication by `s ^ (n + 1)`. -/
def koszulConeTowerSemilinearObjIso (C : CochainComplex 𝒜 ℤ) (n : ℕ) :
    (koszulConeTower r C ⋙ H.mapHomologicalComplex (ComplexShape.up ℤ)).obj ⟨n⟩ ≅
      (koszulConeTower s ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).obj ⟨n⟩ :=
  mappingCone.mapHomologicalComplexIso _ H ≪≫
    mappingCone.isoOfEq (mapHomologicalComplex_map_pow_smul_id H hrs (n + 1) C)

/-- The forward map of `koszulConeTowerSemilinearObjIso` is the comparison of the image of a
mapping cone with the mapping cone of the image, followed by the identification of the mapping
cones of equal morphisms. -/
@[simp]
theorem koszulConeTowerSemilinearObjIso_hom (C : CochainComplex 𝒜 ℤ) (n : ℕ) :
    (koszulConeTowerSemilinearObjIso H hrs C n).hom =
      (mappingCone.mapHomologicalComplexIso (r ^ (n + 1) • 𝟙 C) H).hom ≫
        (mappingCone.isoOfEq
          (mapHomologicalComplex_map_pow_smul_id H hrs (n + 1) C)).hom := rfl

/-- **An additive functor carries one Koszul tower of cones to the other**, compatibly with the
transition maps, as soon as it carries multiplication by `r` to multiplication by `s`. -/
def koszulConeTowerSemilinearMap (C : CochainComplex 𝒜 ℤ) :
    koszulConeTower r C ⋙ H.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      koszulConeTower s ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  NatTrans.ofOpSequence (fun n ↦ (koszulConeTowerSemilinearObjIso H hrs C n).hom) (by
    intro n
    simp only [koszulConeTowerSemilinearObjIso_hom, mappingCone.isoOfEq_hom, Functor.comp_map,
      koszulConeTower, Functor.ofOpSequence_map_homOfLE_succ]
    refine Eq.trans (mappingCone.mapHomologicalComplexIso_hom_map_assoc H _ _ _ _ _ _) ?_
    exact Eq.trans (congrArg (fun t ↦ (mappingCone.mapHomologicalComplexIso
          (r ^ (n + 1 + 1) • 𝟙 C) H).hom ≫ t)
        (mappingCone.map_comp_map_eq _ _ _ _ _ _ _ _
          (by rw [Category.comp_id, Category.id_comp,
            mapHomologicalComplex_map_smul_id H hrs]) (by simp)))
      (Category.assoc _ _ _).symm)

/-- The comparison `koszulConeTowerSemilinearMap` of Koszul towers of cones is an isomorphism. -/
instance isIso_koszulConeTowerSemilinearMap (C : CochainComplex 𝒜 ℤ) :
    IsIso (koszulConeTowerSemilinearMap H hrs C) := by
  have hi (n : ℕᵒᵖ) : IsIso ((koszulConeTowerSemilinearMap H hrs C).app n) := by
    change IsIso (koszulConeTowerSemilinearObjIso H hrs C n.unop).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **An additive functor carries one Koszul tower of cones to the other**, as an isomorphism of
inverse systems. -/
def koszulConeTowerSemilinearIso (C : CochainComplex 𝒜 ℤ) :
    koszulConeTower r C ⋙ H.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      koszulConeTower s ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  asIso (koszulConeTowerSemilinearMap H hrs C)

end Semilinear

end CochainComplex


/-! ### The base ring acting on sheaves of modules on a ringed site -/

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

open scoped IsMulCommutative

variable (X : RingedSite.{u, u, u})

/-- **Multiplication by a global section of `𝒪`, as a ring map into the centre of the category of
sheaves of `𝒪`-modules.** A compatible family of local sections acts on every sheaf of modules,
naturally in the sheaf, and that assignment is a ring homomorphism. -/
def sectionsRingHom : RingCat.sectionsSubring (ringSheaf X.O).obj →+*
    CatCenter (SheafOfModules.{u} (ringSheaf X.O)) where
  toFun s := Stacks.SheafOfModules.globalSectionToEnd (ringSheaf X.O) ⟨s.1, s.2⟩
  map_one' := by
    ext M U x
    change (1 : (ringSheaf X.O).obj.obj U) • x = x
    rw [one_smul]
  map_mul' a b := by
    ext M U x
    rw [CatCenter.mul_app]
    change (a.1 U * b.1 U) • x = b.1 U • a.1 U • x
    rw [mul_comm', mul_smul]
  map_zero' := by
    ext M U x
    change (0 : (ringSheaf X.O).obj.obj U) • x = 0
    rw [zero_smul]
  map_add' a b := by
    ext M U x
    change (a.1 U + b.1 U) • x = a.1 U • x + b.1 U • x
    rw [add_smul]

variable (A : Type u) [CommRing A] (ρ : A →+* RingCat.sectionsSubring (ringSheaf X.O).obj)

/-- **Sheaves of `𝒪`-modules form an `A`-linear category** when `𝒪` is a sheaf of `A`-algebras: a
scalar acts by multiplication by the global section it is sent to. -/
@[instance_reducible]
def linearBaseRingSheaf : Linear A (SheafOfModules.{u} (ringSheaf X.O)) :=
  Linear.ofRingMorphism ((sectionsRingHom X).comp ρ)

/-- A scalar acts on the identity by the central endomorphism its image defines. -/
theorem base_smul_id (a : A) (M : SheafOfModules.{u} (ringSheaf X.O)) :
    letI := linearBaseRingSheaf X A ρ
    a • 𝟙 M = (sectionsRingHom X (ρ a)).app M :=
  Category.comp_id _

/-- **`A`-linear global sections are `A`-linear.** Multiplication by the image of `a` in
`Γ(𝒞, 𝒪)` on a sheaf of `𝒪`-modules becomes multiplication by `a` on its `A`-module of global
sections: the `A`-action on `Γ(𝒞, ℱ) = Hom_𝒪(𝒪, ℱ)` is precomposition with multiplication by
`ρ a` on `𝒪` and the functor acts by postcomposition, so the two agree by naturality. -/
theorem map_smul_id_moduleGlobalSectionsOver (a : A) (M : SheafOfModules.{u} (ringSheaf X.O)) :
    letI := linearBaseRingSheaf X A ρ
    (moduleGlobalSectionsOver X A ρ).map (a • 𝟙 M) =
      a • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj M) := by
  let := linearBaseRingSheaf X A ρ
  rw [base_smul_id X A ρ a M]
  ext t
  have h1 : ((moduleGlobalSectionsOver X A ρ).map ((sectionsRingHom X (ρ a)).app M)).hom t =
      (t : SheafOfModules.unit (ringSheaf X.O) ⟶ M) ≫ (sectionsRingHom X (ρ a)).app M := rfl
  have h2 : (a • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj M)).hom t =
      (a • t : (moduleGlobalSectionsOver X A ρ).obj M) := by simp
  rw [h1, h2, smul_moduleGlobalSectionsOver]
  exact (sectionsRingHom X (ρ a)).naturality
    (t : SheafOfModules.unit (ringSheaf X.O) ⟶ M)

/-- **The complex-level comparison `Q(Γ(𝒞, C)) ⟶ RΓ(𝒞, Q C)`**, the unit of the right derived
functor `derivedGlobalSectionsOverUnbounded` read on cochain complexes. -/
abbrev globalSectionsComplexUnit :
    (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedGlobalSectionsOverUnbounded X A ρ :=
  Stacks.Injectives.complexUnit (moduleGlobalSectionsOver X A ρ)
    (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ)

/-- **K-injective complexes compute derived global sections**: the complex-level comparison is
invertible at every K-injective complex of sheaves of `𝒪`-modules. -/
theorem isIso_globalSectionsComplexUnit_app
    (I : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (hI : I.IsKInjective) :
    IsIso ((globalSectionsComplexUnit X A ρ).app I) :=
  Stacks.Injectives.isIso_complexUnit_app _ _ _ I

/-- An isomorphism in `D(A)` into a K-injective complex is realised by a morphism of complexes. -/
private theorem _root_.CochainComplex.exists_isIso_Q_map_of_isKInjective
    {C I : CochainComplex (ModuleCat.{u} A) ℤ} [I.IsKInjective]
    (e : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj I) :
    ∃ ψ : C ⟶ I, IsIso (DerivedCategory.Q.map ψ) := by
  let cq := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj C)
    I).surjective (cq.hom.app C ≫ e.hom ≫ cq.inv.app I)
  let ψ : C ⟶ I := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).preimage h
  refine ⟨ψ, ?_⟩
  have hnat : DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map ψ) ≫
        cq.hom.app I = cq.hom.app C ≫ DerivedCategory.Q.map ψ :=
    cq.hom.naturality ψ
  rw [Functor.map_preimage, hh] at hnat
  have h₁ : IsIso (cq.hom.app C ≫ DerivedCategory.Q.map ψ) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (cq.hom.app C) _

/-! ### The projection formula -/

/-- **Derived global sections carry the `f`-power Koszul tower of `E` to the `f`-power Koszul
tower of `RΓ(𝒞, E)`.** Let `(𝒞, 𝒪)` be a ringed site, let `ρ : A ⟶ Γ(𝒞, 𝒪)` be a homomorphism
from a commutative ring `A`, let `f ∈ A` and let `E` be a cochain complex of sheaves of
`𝒪`-modules. There is an isomorphism of inverse systems in `D(A)`

`RΓ(𝒞, E ⊗_𝒪 (𝒪 --f^(n+1)--> 𝒪)) ≅ RΓ(𝒞, E) ⊗^𝐋_A (A --f^(n+1)--> A)`,

compatible with the transition maps. Nothing is assumed of the site, of the sheaf of algebras or
of the complex. -/
theorem nonempty_iso_koszulConeTower_derivedGlobalSections (f : A)
    (E : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) :
    letI := linearBaseRingSheaf X A ρ
    Nonempty (CochainComplex.koszulConeTower f E ⋙ DerivedCategory.Q ⋙
        derivedGlobalSectionsOverUnbounded X A ρ ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f
        ((derivedGlobalSectionsOverUnbounded X A ρ).obj (DerivedCategory.Q.obj E))) := by
  let := linearBaseRingSheaf X A ρ
  let G := (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (ringSheaf X.O))).obj E
  let j : E ⟶ J :=
    (Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (ringSheaf X.O))).app E
  have hjQ : IsIso (DerivedCategory.Q.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ j).2 inferInstance
  let e₁ : CochainComplex.koszulConeTower f E ⋙ DerivedCategory.Q ≅
      CochainComplex.koszulConeTower f J ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight (CochainComplex.koszulConeTowerMap f j) DerivedCategory.Q)
  have hunit : IsIso (Functor.whiskerLeft (CochainComplex.koszulConeTower f J)
      (globalSectionsComplexUnit X A ρ)) := by
    have hi (n : ℕᵒᵖ) : IsIso ((Functor.whiskerLeft (CochainComplex.koszulConeTower f J)
        (globalSectionsComplexUnit X A ρ)).app n) :=
      isIso_globalSectionsComplexUnit_app X A ρ _ (CochainComplex.isKInjective_mappingCone _)
    exact NatIso.isIso_of_isIso_app _
  let e₂ : CochainComplex.koszulConeTower f J ⋙ G ⋙ DerivedCategory.Q ≅
      CochainComplex.koszulConeTower f J ⋙ DerivedCategory.Q ⋙
        derivedGlobalSectionsOverUnbounded X A ρ :=
    asIso (Functor.whiskerLeft (CochainComplex.koszulConeTower f J)
      (globalSectionsComplexUnit X A ρ))
  let K := (derivedGlobalSectionsOverUnbounded X A ρ).obj (DerivedCategory.Q.obj E)
  let P := DerivedCategory.Q.objPreimage K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{u} A)).obj P
  let p : P ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)).app P
  have hpQ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance
  have hJunit : IsIso ((globalSectionsComplexUnit X A ρ).app J) :=
    isIso_globalSectionsComplexUnit_app X A ρ J inferInstance
  let u : DerivedCategory.Q.obj (G.obj J) ≅ DerivedCategory.Q.obj I :=
    asIso ((globalSectionsComplexUnit X A ρ).app J) ≪≫
      (derivedGlobalSectionsOverUnbounded X A ρ).mapIso (asIso (DerivedCategory.Q.map j)).symm ≪≫
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ asIso (DerivedCategory.Q.map p)
  obtain ⟨ψ, hψ⟩ := CochainComplex.exists_isIso_Q_map_of_isKInjective A u
  let e₄ : PrincipalTorsionTower.principalComplexSystem A f (G.obj J) ⋙ DerivedCategory.Q ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f K :=
    asIso (Functor.whiskerRight
        (Stacks.Cohomology.KoszulTowerSections.principalComplexSystemMap f ψ)
        DerivedCategory.Q) ≪≫
      (asIso (Functor.whiskerRight
        (Stacks.Cohomology.KoszulTowerSections.principalComplexSystemMap f p)
        DerivedCategory.Q)).symm
  exact ⟨Functor.isoWhiskerRight e₁ (derivedGlobalSectionsOverUnbounded X A ρ) ≪≫
    Functor.associator _ _ _ ≪≫ e₂.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CochainComplex.koszulConeTowerSemilinearIso
      (moduleGlobalSectionsOver X A ρ) (map_smul_id_moduleGlobalSectionsOver X A ρ f) J)
      DerivedCategory.Q ≪≫ e₄⟩

end AlgebraicGeometry.RingedSite

end
