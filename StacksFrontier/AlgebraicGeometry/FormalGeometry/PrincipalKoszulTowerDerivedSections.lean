module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveSubcategory
public import StacksFrontier.Homology.DerivedComplete.PrincipalTorsionTower
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems

/-!
# Derived sections carry the Koszul tower of a complex to the Koszul tower of its sections

Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative
ring `A`, let `f ∈ A` and let `E` be a cochain complex of sheaves of `𝒪_X`-modules. The
`f`-power Koszul tower of `E` is the inverse system `n ↦ E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)`, which
is the system of cones of multiplication by `f^(n+1)` on `E`. This file proves that derived
sections over the base ring carry it to the `f`-power Koszul tower of `RΓ(X, E)` over `A`:

`RΓ(X, E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)) ≅ RΓ(X, E) ⊗^L_A (A --f^(n+1)--> A)`,

compatibly with the transition maps, that is, as an isomorphism of inverse systems `ℕᵒᵖ ⥤ D(A)`.
This is the levelwise identification that the proof of [Stacks, Tag 0H3C] asserts with details
left out, and it is the one input of the displayed equality of [Stacks, Tag 0BLD].

The proof is the obvious one once the models are lined up. Multiplication by `f^(n+1)` is natural
in the complex, so a K-injective resolution `E ⟶ J` induces a map of Koszul towers whose terms
are quasi-isomorphisms; the terms of the Koszul tower of `J` are cones of maps between K-injective
complexes, hence K-injective, so the unit of the right derived functor is invertible on them and
`RΓ` of each term is computed by applying termwise sections. Termwise sections, being an additive
functor, commute with mapping cones, and they carry multiplication by the image of `f` to
multiplication by `f`, which is the whole content of the levelwise identification; the transition
maps are induced by multiplication by `f` on the source of each cone on both sides, so the
comparison is compatible with them. Finally the resulting tower of cones on the complex
`Γ(X, J)` is compared with the tower on the chosen representative of `RΓ(X, E)` through a
K-injective resolution of the latter.

## Main definitions

* `CochainComplex.mappingCone.isoOfEq` — the identification of the mapping cones of two equal
  morphisms, as the cone map induced by the identity square.
* `Stacks.Cohomology.KoszulTowerSections.koszulComplexTowerMap` — the map of `f`-power Koszul
  towers of complexes of sheaves of modules induced by a map of complexes.
* `Stacks.Cohomology.KoszulTowerSections.principalComplexSystemMap` — the same on the algebraic
  side, for `PrincipalTorsionTower.principalComplexSystem`.
* `Stacks.Cohomology.KoszulTowerSections.sectionsDerivedUnit` — the comparison
  `Q(Γ(X, C)) ⟶ RΓ(X, Q C)` at the level of cochain complexes.
* `Stacks.Cohomology.KoszulTowerSections.ksysIso` — the identification of the inverse system
  `Ksys` of cones of the iterated multiplication by a global section on a sheaf of modules with
  the `f`-power Koszul tower of that sheaf placed in cohomological degree zero.

## Main results

* `CochainComplex.mappingCone.map_comp_map_eq` — two composites of cone maps with the same
  composite vertical maps agree. This is what makes the cone construction functorial on towers.
* `CochainComplex.mappingCone.mapHomologicalComplexIso_hom_map` — the identification of the cone
  of the image with the image of the cone commutes with the cone map of a commuting square. This
  is what makes an additive functor commute with a *tower* of cones, not merely with each cone.
* `Stacks.Cohomology.KoszulTowerSections.sectionsOver_map_baseSmul` — sections over the base ring
  carry multiplication by the image of `f` in `Γ(X, 𝒪_X)` to multiplication by `f`.
* `Stacks.Cohomology.KoszulTowerSections.sectionsKoszulComplexTowerIso` — termwise sections carry
  the `f`-power Koszul tower of complexes of sheaves of modules to the `f`-power Koszul tower of
  complexes of `A`-modules.
* `Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections` — the main
  result: derived sections over the base ring carry the `f`-power Koszul tower of `E` to the
  `f`-power Koszul tower of `RΓ(X, E)`, as inverse systems in `D(A)`.

## Implementation notes

The two towers are already built on the same model — cones of the powers of multiplication by
`f` on a chosen complex, with transitions induced by multiplication by `f` on the source and the
identity on the target — so no translation between models intervenes. What has to be supplied is
the compatibility of Mathlib's `mapHomologicalComplexIso` with `mappingCone.map`, which is proved
here by the extensionality of maps out of a cone.

The algebraic Koszul tower `PrincipalTorsionTower.principalDerivedTensorSystem` is built on
`DerivedCategory.Q.objPreimage`, an unspecified representative of the object of `D(A)`. Passing
from the representative `Γ(X, J)` produced by the argument to that one needs a morphism of
complexes, which an isomorphism in `D(A)` does not directly provide; it is obtained by resolving
the representative by a K-injective complex, where morphisms out of the homotopy category are in
bijection with morphisms in `D(A)`, and lifting along the fullness of the quotient functor.

K-injective resolutions are taken with `Stacks.Injectives.kInjectiveResolutionFunctor`, which
needs only that the source be Grothendieck abelian. The resolution of
`CochainComplex.exists_quasiIso_isKInjective` is not available for sheaves of modules, which do
not have exact countable products.

## References

* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open CategoryTheory.Preadditive CategoryTheory.Linear CategoryTheory.Category
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open Opposite TopologicalSpace
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open RingedSpaceModuleAdjunction
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)

universe u

/-! ### An additive functor commutes with a tower of mapping cones -/

namespace CochainComplex.mappingCone

section

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- **The mapping cones of two equal morphisms agree.** The identification is the cone map
induced by the square with identity vertical maps, so that it composes with other cone maps
through `CochainComplex.mappingCone.map_comp`. -/
def isoOfEq {K L : CochainComplex C ℤ} {φ φ' : K ⟶ L} (h : φ = φ') :
    mappingCone φ ≅ mappingCone φ' where
  hom := map φ φ' (𝟙 K) (𝟙 L) (by rw [h, id_comp, comp_id])
  inv := map φ' φ (𝟙 K) (𝟙 L) (by rw [h, id_comp, comp_id])
  hom_inv_id := by rw [← map_comp]; simpa using map_id φ
  inv_hom_id := by rw [← map_comp]; simpa using map_id φ'

/-- The forward map of `isoOfEq h` is the map of cones induced by the identity vertical maps. -/
@[simp]
lemma isoOfEq_hom {K L : CochainComplex C ℤ} {φ φ' : K ⟶ L} (h : φ = φ') :
    (isoOfEq h).hom = map φ φ' (𝟙 K) (𝟙 L) (by rw [h, id_comp, comp_id]) := rfl

/-- **Two composites of cone maps with the same composite vertical maps agree.** Applied to the
transition maps of a tower of cones, this is the compatibility that makes a map of complexes
induce a map of towers. -/
lemma map_comp_map_eq {K₁ L₁ K₂ L₂ K₂' L₂' K₃ L₃ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₂' : K₂' ⟶ L₂') (φ₃ : K₃ ⟶ L₃)
    {a₁ : K₁ ⟶ K₂} {b₁ : L₁ ⟶ L₂} (c₁ : φ₁ ≫ b₁ = a₁ ≫ φ₂)
    {a₂ : K₂ ⟶ K₃} {b₂ : L₂ ⟶ L₃} (c₂ : φ₂ ≫ b₂ = a₂ ≫ φ₃)
    {a₁' : K₁ ⟶ K₂'} {b₁' : L₁ ⟶ L₂'} (c₁' : φ₁ ≫ b₁' = a₁' ≫ φ₂')
    {a₂' : K₂' ⟶ K₃} {b₂' : L₂' ⟶ L₃} (c₂' : φ₂' ≫ b₂' = a₂' ≫ φ₃)
    (ha : a₁ ≫ a₂ = a₁' ≫ a₂') (hb : b₁ ≫ b₂ = b₁' ≫ b₂') :
    map φ₁ φ₂ a₁ b₁ c₁ ≫ map φ₂ φ₃ a₂ b₂ c₂ =
      map φ₁ φ₂' a₁' b₁' c₁' ≫ map φ₂' φ₃ a₂' b₂' c₂' := by
  rw [← map_comp, ← map_comp]
  simp only [ha, hb]

end

section

variable {C : Type*} {D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  (H : C ⥤ D) [H.Additive]

/-- **An additive functor commutes with the cone map of a commuting square.** The isomorphism
`CochainComplex.mappingCone.mapHomologicalComplexIso` identifying the image of a cone with the
cone of the image is compatible with the morphisms of cones induced by commuting squares; it is
therefore an isomorphism of *towers* of cones, which is what a comparison of Koszul towers
needs. -/
@[reassoc]
lemma mapHomologicalComplexIso_hom_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (map φ₁ φ₂ a b comm) ≫
        (mapHomologicalComplexIso φ₂ H).hom =
      (mapHomologicalComplexIso φ₁ H).hom ≫
        map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ₁)
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ₂)
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp]) := by
  rw [← Iso.inv_comp_eq]
  apply HomologicalComplex.hom_ext
  intro n
  have h1 : (inl φ₁).v (n + 1) n (by lia) ≫ (map φ₁ φ₂ a b comm).f n ≫
      (fst φ₂).1.v n (n + 1) (by lia) = a.f (n + 1) := by
    dsimp only [map]
    rw [inl_v_desc_f_assoc]
    simp
  have h2 : (inl φ₁).v (n + 1) n (by lia) ≫ (map φ₁ φ₂ a b comm).f n ≫
      (snd φ₂).v n n (add_zero n) = 0 := by
    dsimp only [map]
    rw [inl_v_desc_f_assoc]
    simp
  have h3 : (inr φ₁).f n ≫ (map φ₁ φ₂ a b comm).f n ≫
      (fst φ₂).1.v n (n + 1) (by lia) = 0 := by
    dsimp only [map]
    rw [inr_f_desc_f_assoc]
    simp
  have h4 : (inr φ₁).f n ≫ (map φ₁ φ₂ a b comm).f n ≫
      (snd φ₂).v n n (add_zero n) = b.f n := by
    dsimp only [map]
    rw [inr_f_desc_f_assoc]
    simp
  rw [ext_from_iff _ (n + 1) n rfl]
  refine ⟨?_, ?_⟩
  · dsimp [mapHomologicalComplexIso]
    rw [mapHomologicalComplexXIso_eq _ _ n (n + 1) rfl,
      mapHomologicalComplexXIso_eq _ _ n (n + 1) rfl]
    simp only [mapHomologicalComplexXIso'_hom, mapHomologicalComplexXIso'_inv,
      comp_add, add_comp, assoc, inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, add_zero]
    simp only [← Functor.map_comp_assoc, h1, h2, H.map_zero, zero_comp, add_zero]
    simp [map]
  · dsimp [mapHomologicalComplexIso]
    rw [mapHomologicalComplexXIso_eq _ _ n (n + 1) rfl,
      mapHomologicalComplexXIso_eq _ _ n (n + 1) rfl]
    simp only [mapHomologicalComplexXIso'_hom, mapHomologicalComplexXIso'_inv,
      comp_add, add_comp, assoc, inr_f_fst_v_assoc, inr_f_snd_v_assoc, zero_comp, zero_add]
    simp only [← Functor.map_comp_assoc, h3, h4, H.map_zero, zero_comp, zero_add]
    simp [map]

end

end CochainComplex.mappingCone

namespace Stacks.Cohomology.KoszulTowerSections

open Stacks.Cohomology.DerivedSectionsOverBase
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)

attribute [local instance] HasDerivedCategory.standard

/-! ### Functoriality of the Koszul tower of complexes of sheaves of modules -/

section Sheaves

variable (X : RingedSpace.{u, u}) (a : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))))

/-- Multiplication by a global section is natural in the complex. -/
lemma smulComplex_naturality {C D : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (g : C ⟶ D) :
    (smulComplex X a C).asHom ≫ g = g ≫ (smulComplex X a D).asHom := by
  apply HomologicalComplex.hom_ext
  intro i
  simpa using (a.asHom.naturality (g.f i)).symm

/-- Powers of multiplication by a global section are natural in the complex. -/
lemma smulComplex_pow_naturality
    {C D : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (g : C ⟶ D) (n : ℕ) :
    (smulComplex X a C ^ n).asHom ≫ g = g ≫ (smulComplex X a D ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, Category.assoc, ih,
      ← Category.assoc, smulComplex_naturality X a g, Category.assoc]

/-- **A map of complexes induces a map of `f`-power Koszul towers.** On the `n`-th term it is the
cone map of the square expressing that the given map commutes with multiplication by
`f^(n+1)`. -/
def koszulComplexTowerMap {C D : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (g : C ⟶ D) :
    principalKoszulComplexTower X a C ⟶ principalKoszulComplexTower X a D :=
  NatTrans.ofOpSequence
    (fun n ↦ CochainComplex.mappingCone.map _ _ g g
      (smulComplex_pow_naturality X a g (n + 1))) (by
    intro n
    simp only [principalKoszulComplexTower, Functor.ofOpSequence_map_homOfLE_succ]
    exact CochainComplex.mappingCone.map_comp_map_eq _ _ _ _ _ _ _ _
      (smulComplex_naturality X a g) (by simp))

/-- If a map of complexes of sheaves of modules is invertible in the derived category then the
induced map of `f`-power Koszul towers is invertible levelwise: the cone of a quasi-isomorphism
of two-term Koszul data is a quasi-isomorphism. -/
instance isIso_whiskerRight_koszulComplexTowerMap
    {C D : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (g : C ⟶ D)
    [IsIso (DerivedCategory.Q.map g)] :
    IsIso (Functor.whiskerRight (koszulComplexTowerMap X a g) DerivedCategory.Q) := by
  have hi (n : ℕᵒᵖ) :
      IsIso ((Functor.whiskerRight (koszulComplexTowerMap X a g) DerivedCategory.Q).app n) := by
    refine isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap
          (smulComplex X a C ^ (n.unop + 1)).asHom (smulComplex X a D ^ (n.unop + 1)).asHom g g
            (smulComplex_pow_naturality X a g (n.unop + 1))))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) ?_ ?_
    · change IsIso (DerivedCategory.Q.map g); infer_instance
    · change IsIso (DerivedCategory.Q.map g); infer_instance
  exact NatIso.isIso_of_isIso_app _

end Sheaves

/-! ### Functoriality of the algebraic Koszul tower -/

section Modules

variable {A : Type u} [CommRing A] (f : A)

/-- **A map of complexes of `A`-modules induces a map of `f`-power Koszul towers.** This is the
algebraic counterpart of `koszulComplexTowerMap`. -/
def principalComplexSystemMap {C D : CochainComplex (ModuleCat.{u} A) ℤ} (g : C ⟶ D) :
    PrincipalTorsionTower.principalComplexSystem A f C ⟶
      PrincipalTorsionTower.principalComplexSystem A f D :=
  NatTrans.ofOpSequence
    (fun n ↦ CochainComplex.mappingCone.map _ _ g g (by
      simp [smul_comp, comp_smul])) (by
    intro n
    simp only [PrincipalTorsionTower.principalComplexSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact CochainComplex.mappingCone.map_comp_map_eq _ _ _ _ _ _ _ _
      (by simp [smul_comp, comp_smul]) (by simp))

/-- A map of complexes of `A`-modules which is invertible in `D(A)` induces a levelwise
isomorphism of `f`-power Koszul towers. -/
instance isIso_whiskerRight_principalComplexSystemMap
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (g : C ⟶ D)
    [IsIso (DerivedCategory.Q.map g)] :
    IsIso (Functor.whiskerRight (principalComplexSystemMap f g) DerivedCategory.Q) := by
  have hi (n : ℕᵒᵖ) :
      IsIso ((Functor.whiskerRight (principalComplexSystemMap f g) DerivedCategory.Q).app n) := by
    refine isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap
          (f ^ (n.unop + 1) • 𝟙 C) (f ^ (n.unop + 1) • 𝟙 D) g g (by simp [smul_comp, comp_smul])))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) ?_ ?_
    · change IsIso (DerivedCategory.Q.map g); infer_instance
    · change IsIso (DerivedCategory.Q.map g); infer_instance
  exact NatIso.isIso_of_isIso_app _

end Modules

/-! ### Sections over the base ring carry one Koszul tower to the other -/

section Sections

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) (f : A)

/-- **Sections over the base ring are `A`-linear.** Multiplication by the image of `f` in
`Γ(X, 𝒪_X)` on a sheaf of modules becomes multiplication by `f` on its `A`-module of sections. -/
lemma sectionsOver_map_baseSmul (M : SheafOfModules.{u} (structureSheafRing X)) :
    (sectionsOver X ρ).map ((baseSmul X ρ f).asHom.app M) = f • 𝟙 ((sectionsOver X ρ).obj M) := by
  ext (x : M.val.obj (op ⊤))
  change ((baseSmul X ρ f).asHom.app M).val.app (op ⊤) x = _
  rw [Stacks.SheafOfModules.terminalSectionToEnd_apply]
  change (structureSheafRing X).obj.map (isTerminalTop.from ⊤).op (ρ f) • x = ρ f • x
  have h : (isTerminalTop.from (⊤ : Opens X.carrier)).op = 𝟙 (op (⊤ : Opens X.carrier)) :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [h, (structureSheafRing X).obj.map_id]
  rfl

/-- Termwise sections over the base ring carry multiplication by the image of `f` on a complex of
sheaves of modules to multiplication by `f` on the complex of sections. -/
lemma mapHomologicalComplex_map_smulComplex
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (smulComplex X (baseSmul X ρ f) C).asHom =
      f • 𝟙 (((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  exact HomologicalComplex.hom_ext _ _ fun i => sectionsOver_map_baseSmul X ρ f (C.X i)

/-- Termwise sections over the base ring carry the powers of multiplication by the image of `f`
to the powers of multiplication by `f`. -/
lemma mapHomologicalComplex_map_smulComplex_pow
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℕ) :
    ((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (smulComplex X (baseSmul X ρ f) C ^ n).asHom =
      f ^ n • 𝟙 (((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, End.mul_asHom, Functor.map_comp, ih, mapHomologicalComplex_map_smulComplex,
      pow_succ]
    simp only [Linear.comp_smul, Category.comp_id, smul_smul, mul_comm]

/-- The levelwise comparison of `sectionsKoszulComplexTowerIso`: termwise sections of the cone of
multiplication by `f^(n+1)` is the cone of multiplication by `f^(n+1)` on the sections. -/
def sectionsKoszulComplexTowerObjIso
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℕ) :
    (principalKoszulComplexTower X (baseSmul X ρ f) C ⋙
        (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj ⟨n⟩ ≅
      (PrincipalTorsionTower.principalComplexSystem A f
        (((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).obj ⟨n⟩ :=
  CochainComplex.mappingCone.mapHomologicalComplexIso _ (sectionsOver X ρ) ≪≫
    CochainComplex.mappingCone.isoOfEq
      (mapHomologicalComplex_map_smulComplex_pow X ρ f C (n + 1))

/-- The forward map of `sectionsKoszulComplexTowerObjIso` is the composite of the forward maps of
`CochainComplex.mappingCone.mapHomologicalComplexIso` and `CochainComplex.mappingCone.isoOfEq`. -/
@[simp]
lemma sectionsKoszulComplexTowerObjIso_hom
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℕ) :
    (sectionsKoszulComplexTowerObjIso X ρ f C n).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso
          (smulComplex X (baseSmul X ρ f) C ^ (n + 1)).asHom (sectionsOver X ρ)).hom ≫
        (CochainComplex.mappingCone.isoOfEq
          (mapHomologicalComplex_map_smulComplex_pow X ρ f C (n + 1))).hom := rfl

/-- **Termwise sections carry one Koszul tower of complexes to the other.** Sections over the base
ring take the `f`-power Koszul tower of a complex of sheaves of `𝒪_X`-modules to the `f`-power
Koszul tower of the complex of its sections, compatibly with the transition maps. -/
def sectionsKoszulComplexTowerMap
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    principalKoszulComplexTower X (baseSmul X ρ f) C ⋙
        (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      PrincipalTorsionTower.principalComplexSystem A f
        (((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  NatTrans.ofOpSequence (fun n ↦ (sectionsKoszulComplexTowerObjIso X ρ f C n).hom) (by
    intro n
    simp only [sectionsKoszulComplexTowerObjIso_hom,
      CochainComplex.mappingCone.isoOfEq_hom, Functor.comp_map,
      principalKoszulComplexTower, PrincipalTorsionTower.principalComplexSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    refine Eq.trans (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_map_assoc
      (sectionsOver X ρ) _ _ _ _ _ _) ?_
    exact Eq.trans (congrArg (fun t ↦ (CochainComplex.mappingCone.mapHomologicalComplexIso
          (smulComplex X (baseSmul X ρ f) C ^ (n + 1 + 1)).asHom (sectionsOver X ρ)).hom ≫ t)
        (CochainComplex.mappingCone.map_comp_map_eq _ _ _ _ _ _ _ _
          (by rw [comp_id, id_comp, mapHomologicalComplex_map_smulComplex]) (by simp)))
      (Category.assoc _ _ _).symm)

/-- The map of towers of complexes `sectionsKoszulComplexTowerMap` is an isomorphism. -/
instance isIso_sectionsKoszulComplexTowerMap
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsIso (sectionsKoszulComplexTowerMap X ρ f C) := by
  have hi (n : ℕᵒᵖ) : IsIso ((sectionsKoszulComplexTowerMap X ρ f C).app n) := by
    change IsIso (sectionsKoszulComplexTowerObjIso X ρ f C n.unop).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **Termwise sections carry one Koszul tower of complexes to the other**, as an isomorphism. -/
def sectionsKoszulComplexTowerIso
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    principalKoszulComplexTower X (baseSmul X ρ f) C ⋙
        (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      PrincipalTorsionTower.principalComplexSystem A f
        (((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  asIso (sectionsKoszulComplexTowerMap X ρ f C)

end Sections

/-! ### The unit of derived sections at a K-injective complex -/

section Unit

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))

/-- **The complex-level comparison `Q(Γ(X, C)) ⟶ RΓ(X, Q C)`.** It is the unit of the right
derived functor `derivedSectionsOver`, read on cochain complexes rather than on the homotopy
category. -/
def sectionsDerivedUnit :
    (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSectionsOver X ρ :=
  ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((sectionsOver X ρ).mapHomotopyCategoryFactors (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))).inv ≫
  Functor.whiskerLeft
    (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (derivedSectionsOverUnit X ρ) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom
    (derivedSectionsOver X ρ)

/-- **K-injective complexes compute derived sections.** The complex-level comparison is invertible
at every K-injective complex of sheaves of `𝒪_X`-modules. -/
lemma isIso_sectionsDerivedUnit_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso ((sectionsDerivedUnit X ρ).app I) := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  have h : IsIso ((derivedSectionsOverUnit X ρ).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((sectionsOver X ρ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ ⟨(Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} (structureSheafRing X))).obj K,
        (Stacks.Injectives.kInjectiveResolutionInclusion
          (SheafOfModules.{u} (structureSheafRing X))).app K, inferInstance, inferInstance⟩)).2
      DerivedCategory.Qh (derivedSectionsOver X ρ) (derivedSectionsOverUnit X ρ) I hI
  dsimp [sectionsDerivedUnit]
  infer_instance

end Unit

/-! ### The main comparison -/

section Main

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) (f : A)

/-- **Derived sections carry the `f`-power Koszul tower of `E` to the `f`-power Koszul tower of
`RΓ(X, E)`.** For a cochain complex `E` of sheaves of `𝒪_X`-modules there is an isomorphism of
inverse systems in `D(A)`

`RΓ(X, E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)) ≅ RΓ(X, E) ⊗^L_A (A --f^(n+1)--> A)`,

compatible with the transition maps. This is the levelwise identification that the proof of
[Stacks, Tag 0H3C] asserts with details left out. -/
theorem nonempty_iso_koszulTower_derivedSections
    (E : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    Nonempty (principalKoszulComplexTower X (baseSmul X ρ f) E ⋙ DerivedCategory.Q ⋙
        derivedSectionsOver X ρ ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f
        ((derivedSectionsOver X ρ).obj (DerivedCategory.Q.obj E))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  let G := (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)
  -- A K-injective resolution of `E`.
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (structureSheafRing X))).obj E
  let j : E ⟶ J :=
    (Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing X))).app E
  have hJ : J.IsKInjective := inferInstance
  have hjQ : IsIso (DerivedCategory.Q.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ j).2 inferInstance
  -- Step 1: replace `E` by `J` in the Koszul tower.
  let e₁ : principalKoszulComplexTower X (baseSmul X ρ f) E ⋙ DerivedCategory.Q ≅
      principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight (koszulComplexTowerMap X (baseSmul X ρ f) j) DerivedCategory.Q)
  -- Step 2: the terms of the Koszul tower of `J` are K-injective, so `RΓ` is computed termwise.
  have hcone (n : ℕ) :
      ((principalKoszulComplexTower X (baseSmul X ρ f) J).obj ⟨n⟩).IsKInjective :=
    CochainComplex.isKInjective_mappingCone _
  have hunit : IsIso (Functor.whiskerLeft
      (principalKoszulComplexTower X (baseSmul X ρ f) J) (sectionsDerivedUnit X ρ)) := by
    have hi (n : ℕᵒᵖ) : IsIso ((Functor.whiskerLeft
        (principalKoszulComplexTower X (baseSmul X ρ f) J)
        (sectionsDerivedUnit X ρ)).app n) :=
      isIso_sectionsDerivedUnit_app X ρ _ (hcone n.unop)
    exact NatIso.isIso_of_isIso_app _
  let e₂ : principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ G ⋙ DerivedCategory.Q ≅
      principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ DerivedCategory.Q ⋙
        derivedSectionsOver X ρ :=
    asIso (Functor.whiskerLeft
      (principalKoszulComplexTower X (baseSmul X ρ f) J) (sectionsDerivedUnit X ρ))
  -- Step 3: termwise sections carry one tower of cones to the other.
  let e₃ : principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ G ≅
      PrincipalTorsionTower.principalComplexSystem A f (G.obj J) :=
    sectionsKoszulComplexTowerIso X ρ f J
  -- Step 4: compare the representative `Γ(X, J)` with the chosen representative of `RΓ(X, E)`.
  let K := (derivedSectionsOver X ρ).obj (DerivedCategory.Q.obj E)
  let P := DerivedCategory.Q.objPreimage K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{u} A)).obj P
  let p : P ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)).app P
  have hI : I.IsKInjective := inferInstance
  have hpQ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance
  -- The identification of `Q(Γ(X, J))` with `Q I` in `D(A)`.
  have hJunit : IsIso ((sectionsDerivedUnit X ρ).app J) :=
    isIso_sectionsDerivedUnit_app X ρ J hJ
  let u : DerivedCategory.Q.obj (G.obj J) ≅ DerivedCategory.Q.obj I :=
    asIso ((sectionsDerivedUnit X ρ).app J) ≪≫
      (derivedSectionsOver X ρ).mapIso (asIso (DerivedCategory.Q.map j)).symm ≪≫
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ asIso (DerivedCategory.Q.map p)
  -- Realise it by a morphism of complexes, using that `I` is K-injective.
  let cq := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj (G.obj J))
    I).surjective (cq.hom.app (G.obj J) ≫ u.hom ≫ cq.inv.app I)
  let ψ : G.obj J ⟶ I :=
    (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).preimage h
  have hψ : IsIso (DerivedCategory.Q.map ψ) := by
    have hnat : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map ψ) ≫
          cq.hom.app I = cq.hom.app (G.obj J) ≫ DerivedCategory.Q.map ψ :=
      cq.hom.naturality ψ
    rw [Functor.map_preimage, hh] at hnat
    have h₁ : IsIso (cq.hom.app (G.obj J) ≫ DerivedCategory.Q.map ψ) := by
      rw [← hnat]; infer_instance
    exact IsIso.of_isIso_comp_left (cq.hom.app (G.obj J)) _
  let e₄ : PrincipalTorsionTower.principalComplexSystem A f (G.obj J) ⋙ DerivedCategory.Q ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f K :=
    asIso (Functor.whiskerRight (principalComplexSystemMap f ψ) DerivedCategory.Q) ≪≫
      (asIso (Functor.whiskerRight (principalComplexSystemMap f p) DerivedCategory.Q)).symm
  exact ⟨Functor.isoWhiskerRight e₁ (derivedSectionsOver X ρ) ≪≫
    Functor.associator _ _ _ ≪≫ e₂.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₃ DerivedCategory.Q ≪≫ e₄⟩

end Main

/-! ### The Koszul tower of a sheaf of modules placed in degree zero -/

section Single

variable (X : RingedSpace.{u, u}) (a : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))))

/-- Multiplication by a global section on a sheaf of modules placed in cohomological degree zero
is multiplication by that section on the single complex. -/
lemma smulComplex_single (M : SheafOfModules.{u} (structureSheafRing X)) :
    (smulComplex X a (sgl.obj M)).asHom = sgl.map (a.asHom.app M) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst h
    simp only [smulComplex_f, HomologicalComplex.single_map_f_self, Functor.id_obj]
    have hn := a.asHom.naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom
    simp only [Functor.id_map, Functor.id_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_src _ _

/-- The single-complex functor carries the `n`-fold composite of multiplication by a global
section to the `n`-th power of multiplication by that section on the single complex. -/
lemma single_map_iterate (M : SheafOfModules.{u} (structureSheafRing X)) (n : ℕ) :
    sgl.map (iterate (a.asHom.app M) n) = (smulComplex X a (sgl.obj M) ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ, Functor.map_comp, ih, pow_succ, End.mul_asHom, smulComplex_single]

/-- **The Koszul tower of a sheaf of modules in degree zero.** The inverse system `Ksys` of cones
of the iterated multiplication by a global section on a sheaf of modules is the `f`-power Koszul
tower of that sheaf placed in cohomological degree zero. -/
def ksysMap (M : SheafOfModules.{u} (structureSheafRing X)) :
    Ksys (a.asHom.app M) ⟶ principalKoszulComplexTower X a (sgl.obj M) ⋙ DerivedCategory.Q :=
  NatTrans.ofOpSequence
    (fun n ↦ DerivedCategory.Q.map
      (CochainComplex.mappingCone.isoOfEq (single_map_iterate X a M (n + 1))).hom) (by
    intro n
    simp only [Ksys, Ktrans, Functor.comp_map, principalKoszulComplexTower,
      Functor.ofOpSequence_map_homOfLE_succ, CochainComplex.mappingCone.isoOfEq_hom]
    refine Eq.trans (DerivedCategory.Q.map_comp _ _).symm (Eq.trans
      (congrArg DerivedCategory.Q.map
        (CochainComplex.mappingCone.map_comp_map_eq _ _ _ _ _ _ _ _ ?_ ?_))
      (DerivedCategory.Q.map_comp _ _))
    · rw [comp_id, id_comp, smulComplex_single]
    · simp)

/-- The map of towers in the derived category `ksysMap` is an isomorphism. -/
instance isIso_ksysMap (M : SheafOfModules.{u} (structureSheafRing X)) : IsIso (ksysMap X a M) := by
  have hi (n : ℕᵒᵖ) : IsIso ((ksysMap X a M).app n) := by
    change IsIso (DerivedCategory.Q.map
      (CochainComplex.mappingCone.isoOfEq (single_map_iterate X a M (n.unop + 1))).hom)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **The Koszul tower of a sheaf of modules in degree zero**, as an isomorphism. -/
def ksysIso (M : SheafOfModules.{u} (structureSheafRing X)) :
    Ksys (a.asHom.app M) ≅ principalKoszulComplexTower X a (sgl.obj M) ⋙ DerivedCategory.Q :=
  asIso (ksysMap X a M)

end Single

end Stacks.Cohomology.KoszulTowerSections

end
