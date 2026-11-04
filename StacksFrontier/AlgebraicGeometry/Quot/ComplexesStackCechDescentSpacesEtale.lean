module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentInterface
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleSystemRealizesSubsingleton
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDerivedEquivalence

/-!
# Stacks 0DLA on the spaces-étale sites from Stacks 0D9T without flatness: the reduction

Piece P-0DHF of the 0DLA programme is
`AlgebraicGeometry.Space.SpacesEtaleHypercoverDescentOfRealization`: Stacks 0D9T without its
flatness hypothesis (P-core) gives Stacks 0DLA on the spaces-étale sites. The source's proof runs
0GMF, 0D9T and 0DHF on the simplicial-site situation of the strict components of the
hypercovering `U`. This file carries out that proof, and isolates the four statements about the
strict components that it uses as propositions:

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictPairRealization`: a pair `(K₀, α)` on
  the spaces-étale sites satisfying the cocycle condition comes from a pair of Stacks 0GMF on the
  strict components, through the equivalences `R_n` of the component ringed topoi with the
  spaces-étale ringed topoi of the `U_n`; in degrees `0` and `1` the system of Stacks 0GMF
  realizes to `K₀` and to its pullbacks, with the transitions realizing to `α` and to the
  identity. This is the pseudonaturality of `R` against the composition isomorphisms of
  derived pullbacks (Stacks 0D6D) on both sides.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictAugmentationTransitionCoherent`: for an
  augmentation `a` and `b = a ∘ e⁻¹` its reading on the strict total site, the derived transitions
  of `Lb^*M` realize to the composition isomorphisms `La_n^* ≅ LX(φ)^* La_m^*` through
  `strictAugmentationDegreeDerivedIso` (Stacks 0D7H (4) made explicit).
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictCartesianQuasicoherent`: for an fppf
  hypercovering, a cartesian object of the derived category of the strict total site whose
  components realize to complexes with quasi-coherent cohomology has quasi-coherent cohomology
  on `U_{spaces,étale}` after the comparison `e` (Stacks 0D7L (2), the face transitions being flat,
  and Stacks 0D7M).
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.SpacesEtaleVertexQuasicoherent`: the pullback
  of a complex with quasi-coherent cohomology along a vertex `U_n ⟶ U_0` of an fppf hypercovering
  has quasi-coherent cohomology (the vertices are flat, Stacks 0DER).

The main result is, in the namespace `AlgebraicGeometry.Space`,
`SimplicialSpacesEtaleSite.spacesEtaleHypercoverDescentOfRealization_of_strict`.

## The compatibility in degree one

The comparison `β : La₀^*K ≅ K₀` is read off the degree-zero component of the realizing object,
and its compatibility with `α` (Stacks 0DLA) is a diagram chase in degree one, carried out over
arbitrary categories in `CategoryTheory.pull_inv_comp_hypercoverTriangle_inv`,
`CategoryTheory.hypercoverCompatible_of_strict` and, in the shape of
`CategoryTheory.IsHypercoverDescentCompatible`,
`CategoryTheory.isHypercoverDescentCompatible_of_strict`.
Its input at a face is `CategoryTheory.IsRealizedHypercoverTriangle`, which is how
`StrictAugmentationTransitionCoherent` is stated: kept as a definition, it is compared with the
goal argument by argument rather than unfolded.

## Implementation notes

The global instance `SheafOfModules.hasDerivedCategory` (the locally small model) is removed
here: under these imports it is found before `HasDerivedCategory.standard`, and the derived
categories of the components would then not be those of the base's Stacks 0D9T.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D7L](https://stacks.math.columbia.edu/tag/0D7L)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-! ### The degree-one chase, over arbitrary categories -/

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒜₀ : Type u₁} [Category.{v₁} 𝒜₀] {𝒜₁ : Type u₂} [Category.{v₂} 𝒜₁]
  {𝒞₀ : Type u₃} [Category.{v₃} 𝒞₀] {𝒞₁ : Type u₄} [Category.{v₄} 𝒞₁]

/-- One face of the degree-one chase. `R₀, R₁` realize the strict components, `P` is the pullback
along a face and `L` the derived transition along it, with `sq : L ⋙ R₁ ≅ R₀ ⋙ P`. The realizing
system has components `T₀, T₁` and transition `t`; the pulled-back object has components
`N₀, N₁` and transition `n`, identified with `T` by `ρ`; `Θ` realizes `N` to the pullbacks `Q`
along the augmentation, and `tri` compares them. If the transition `n` realizes to `tri`, then
pulling `β = Θ₀⁻¹ ≫ R₀ ρ₀⁻¹ ≫ ε₀` back along the face and following with `tri⁻¹` is the
realization of `t`, followed by `ρ₁` and `Θ₁`. -/
theorem pull_inv_comp_hypercoverTriangle_inv (P : 𝒜₀ ⥤ 𝒜₁) (L : 𝒞₀ ⥤ 𝒞₁) (R₀ : 𝒞₀ ⥤ 𝒜₀)
    (R₁ : 𝒞₁ ⥤ 𝒜₁) (sq : L ⋙ R₁ ≅ R₀ ⋙ P) {T₀ N₀ : 𝒞₀} {T₁ N₁ : 𝒞₁} {K₀ Q₀ : 𝒜₀} {Q₁ : 𝒜₁}
    (t : L.obj T₀ ⟶ T₁) (n : L.obj N₀ ⟶ N₁) (ρ₀ : T₀ ≅ N₀) (ρ₁ : T₁ ≅ N₁)
    (hρ : t ≫ ρ₁.hom = L.map ρ₀.hom ≫ n) (Θ₀ : R₀.obj N₀ ≅ Q₀) (Θ₁ : R₁.obj N₁ ≅ Q₁)
    (tri : Q₁ ≅ P.obj Q₀)
    (hn : R₁.map n = sq.hom.app N₀ ≫ P.map Θ₀.hom ≫ tri.inv ≫ Θ₁.inv) (ε₀ : R₀.obj T₀ ≅ K₀) :
    P.map (Θ₀.symm ≪≫ R₀.mapIso ρ₀.symm ≪≫ ε₀).inv ≫ tri.inv =
      P.map ε₀.inv ≫ sq.inv.app T₀ ≫ R₁.map t ≫ R₁.map ρ₁.hom ≫ Θ₁.hom := by
  have htri : tri.inv = P.map Θ₀.inv ≫ sq.inv.app N₀ ≫ R₁.map n ≫ Θ₁.hom := by
    rw [hn]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_app_assoc,
      ← P.map_comp_assoc, Iso.inv_hom_id, P.map_id, Category.id_comp]
  have hnat := sq.inv.naturality ρ₀.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  have hρ' : R₁.map (L.map ρ₀.hom) ≫ R₁.map n = R₁.map t ≫ R₁.map ρ₁.hom := by
    rw [← R₁.map_comp, ← R₁.map_comp, hρ]
  rw [htri]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [← P.map_comp_assoc Θ₀.hom Θ₀.inv, Iso.hom_inv_id, P.map_id, Category.id_comp,
    reassoc_of% hnat, reassoc_of% hρ']

/-- **The degree-one chase of Stacks 0DLA.** With the data of
`CategoryTheory.pull_inv_comp_hypercoverTriangle_inv` at both faces `δ₀, δ₁ : U₁ ⟶ U₀`, if the
realizing system's transitions realize to the identity at `δ₀` and to `α` at `δ₁`, then
`β = Θ₀⁻¹ ≫ R₀ ρ₀⁻¹ ≫ ε₀` is compatible with `α`. -/
theorem hypercoverCompatible_of_strict (P₀ P₁ : 𝒜₀ ⥤ 𝒜₁) (L₀ L₁ : 𝒞₀ ⥤ 𝒞₁) (R₀ : 𝒞₀ ⥤ 𝒜₀)
    (R₁ : 𝒞₁ ⥤ 𝒜₁) (sq₀ : L₀ ⋙ R₁ ≅ R₀ ⋙ P₀) (sq₁ : L₁ ⋙ R₁ ≅ R₀ ⋙ P₁) {T₀ N₀ : 𝒞₀}
    {T₁ N₁ : 𝒞₁} {K₀ : 𝒜₀} (t₀ : L₀.obj T₀ ⟶ T₁) (t₁ : L₁.obj T₀ ⟶ T₁)
    (n₀ : L₀.obj N₀ ⟶ N₁) (n₁ : L₁.obj N₀ ⟶ N₁) (ρ₀ : T₀ ≅ N₀) (ρ₁ : T₁ ≅ N₁)
    (hρ₀ : t₀ ≫ ρ₁.hom = L₀.map ρ₀.hom ≫ n₀) (hρ₁ : t₁ ≫ ρ₁.hom = L₁.map ρ₀.hom ≫ n₁)
    {𝒵 : Type*} [Category 𝒵] {G₀ : 𝒵 ⥤ 𝒜₀} {G₁ : 𝒵 ⥤ 𝒜₁} {M : 𝒵}
    (Θ₀ : R₀.obj N₀ ≅ G₀.obj M) (Θ₁ : R₁.obj N₁ ≅ G₁.obj M) (tri₀ : G₁ ≅ G₀ ⋙ P₀)
    (tri₁ : G₁ ≅ G₀ ⋙ P₁)
    (hn₀ : R₁.map n₀ = sq₀.hom.app N₀ ≫ P₀.map Θ₀.hom ≫ tri₀.inv.app M ≫ Θ₁.inv)
    (hn₁ : R₁.map n₁ = sq₁.hom.app N₀ ≫ P₁.map Θ₀.hom ≫ tri₁.inv.app M ≫ Θ₁.inv)
    (ε₀ : R₀.obj T₀ ≅ K₀) (ε₁ : R₁.obj T₁ ≅ P₀.obj K₀) (α : P₁.obj K₀ ≅ P₀.obj K₀)
    (ht₀ : R₁.map t₀ = sq₀.hom.app T₀ ≫ P₀.map ε₀.hom ≫ ε₁.inv)
    (ht₁ : R₁.map t₁ = sq₁.hom.app T₀ ≫ P₁.map ε₀.hom ≫ α.hom ≫ ε₁.inv) :
    P₁.map (Θ₀.symm ≪≫ R₀.mapIso ρ₀.symm ≪≫ ε₀).inv ≫ tri₁.inv.app M ≫ tri₀.hom.app M ≫
        P₀.map (Θ₀.symm ≪≫ R₀.mapIso ρ₀.symm ≪≫ ε₀).hom = α.hom := by
  have e₁ := pull_inv_comp_hypercoverTriangle_inv P₁ L₁ R₀ R₁ sq₁ t₁ n₁ ρ₀ ρ₁ hρ₁ Θ₀ Θ₁
    (tri₁.app M) hn₁ ε₀
  have e₀ := pull_inv_comp_hypercoverTriangle_inv P₀ L₀ R₀ R₁ sq₀ t₀ n₀ ρ₀ ρ₁ hρ₀ Θ₀ Θ₁
    (tri₀.app M) hn₀ ε₀
  simp only [Iso.app_inv] at e₁ e₀
  rw [ht₁] at e₁
  rw [ht₀] at e₀
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← P₁.map_comp_assoc, Iso.inv_hom_id,
    P₁.map_id, Category.id_comp] at e₁
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← P₀.map_comp_assoc, Iso.inv_hom_id,
    P₀.map_id, Category.id_comp] at e₀
  have e₀r := congrArg (· ≫ tri₀.hom.app M ≫ P₀.map (Θ₀.symm ≪≫ R₀.mapIso ρ₀.symm ≪≫ ε₀).hom) e₀
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← P₀.map_comp, Iso.inv_hom_id,
    P₀.map_id, Functor.comp_obj] at e₀r
  rw [reassoc_of% e₁, ← e₀r, Category.comp_id]

/-- **A transition realizing a composition triangle.** For a pullback assignment `pull` with
composition comparison `comp`, `f : U₁ ⟶ U₀` and `a₀, a₁` with `f ≫ a₀ = a₁`, a map
`n : L N₀ ⟶ N₁` realizes, through `R₀, R₁`, `sq : L ⋙ R₁ ≅ R₀ ⋙ pull f` and
`Θᵢ : Rᵢ Nᵢ ≅ (pull aᵢ) K`, the triangle `pull a₁ ≅ pull a₀ ⋙ pull f` at `K`. -/
def IsRealizedHypercoverTriangle {A : Type*} [Category A] {D : A → Type*} [∀ a, Category (D a)]
    (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {X U₀ U₁ : A} (a₀ : U₀ ⟶ X) (f : U₁ ⟶ U₀) (a₁ : U₁ ⟶ X) (hk : f ≫ a₀ = a₁)
    (L : 𝒞₀ ⥤ 𝒞₁) (R₀ : 𝒞₀ ⥤ D U₀) (R₁ : 𝒞₁ ⥤ D U₁) (sq : L ⋙ R₁ ≅ R₀ ⋙ pull f)
    {N₀ : 𝒞₀} {N₁ : 𝒞₁} (n : L.obj N₀ ⟶ N₁) (K : D X) (Θ₀ : R₀.obj N₀ ≅ (pull a₀).obj K)
    (Θ₁ : R₁.obj N₁ ≅ (pull a₁).obj K) : Prop :=
  R₁.map n = sq.hom.app N₀ ≫ (pull f).map Θ₀.hom ≫
    (hypercoverPullTriangle pull comp hk).inv.app K ≫ Θ₁.inv

/-- **The degree-one chase of Stacks 0DLA, in the shape of `IsHypercoverDescentCompatible`.** For a
pullback assignment `pull` with composition comparison `comp`, an augmentation `a₀ : U₀ ⟶ X`, faces
`s = δ₁`, `t = δ₀` with `s ≫ a₀ = a₁ = t ≫ a₀`, and the data of
`CategoryTheory.hypercoverCompatible_of_strict` with `P₀ = pull t`, `P₁ = pull s` and the triangles
of `comp`, the comparison `β = Θ₀⁻¹ ≫ R₀ ρ₀⁻¹ ≫ ε₀` is compatible with `α`. -/
theorem isHypercoverDescentCompatible_of_strict {A : Type*} [Category A] {D : A → Type*}
    [∀ a, Category (D a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {X U₀ U₁ : A} (a₀ : U₀ ⟶ X) (s t : U₁ ⟶ U₀) (a₁ : U₁ ⟶ X) (hs : s ≫ a₀ = a₁)
    (ht : t ≫ a₀ = a₁) (L₀ L₁ : 𝒞₀ ⥤ 𝒞₁) (R₀ : 𝒞₀ ⥤ D U₀) (R₁ : 𝒞₁ ⥤ D U₁)
    (sq₀ : L₀ ⋙ R₁ ≅ R₀ ⋙ pull t) (sq₁ : L₁ ⋙ R₁ ≅ R₀ ⋙ pull s) {T₀ N₀ : 𝒞₀}
    {T₁ N₁ : 𝒞₁} {K₀ : D U₀} (K : D X) (t₀ : L₀.obj T₀ ⟶ T₁) (t₁ : L₁.obj T₀ ⟶ T₁)
    (n₀ : L₀.obj N₀ ⟶ N₁) (n₁ : L₁.obj N₀ ⟶ N₁) (ρ₀ : T₀ ≅ N₀) (ρ₁ : T₁ ≅ N₁)
    (hρ₀ : t₀ ≫ ρ₁.hom = L₀.map ρ₀.hom ≫ n₀) (hρ₁ : t₁ ≫ ρ₁.hom = L₁.map ρ₀.hom ≫ n₁)
    (Θ₀ : R₀.obj N₀ ≅ (pull a₀).obj K) (Θ₁ : R₁.obj N₁ ≅ (pull a₁).obj K)
    (hn₀ : IsRealizedHypercoverTriangle pull comp a₀ t a₁ ht L₀ R₀ R₁ sq₀ n₀ K Θ₀ Θ₁)
    (hn₁ : IsRealizedHypercoverTriangle pull comp a₀ s a₁ hs L₁ R₀ R₁ sq₁ n₁ K Θ₀ Θ₁)
    (ε₀ : R₀.obj T₀ ≅ K₀) (ε₁ : R₁.obj T₁ ≅ (pull t).obj K₀)
    (α : (pull s).obj K₀ ≅ (pull t).obj K₀)
    (ht₀ : R₁.map t₀ = sq₀.hom.app T₀ ≫ (pull t).map ε₀.hom ≫ ε₁.inv)
    (ht₁ : R₁.map t₁ = sq₁.hom.app T₀ ≫ (pull s).map ε₀.hom ≫ α.hom ≫ ε₁.inv) :
    IsHypercoverDescentCompatible pull comp a₀ s t α K (Θ₀.symm ≪≫ R₀.mapIso ρ₀.symm ≪≫ ε₀) := by
  intro a₁' hs' ht'
  have e : a₁' = a₁ := hs'.symm.trans hs
  subst e
  exact hypercoverCompatible_of_strict (pull t) (pull s) L₀ L₁ R₀ R₁ sq₀ sq₁ t₀ t₁ n₀ n₁ ρ₀ ρ₁
    hρ₀ hρ₁ Θ₀ Θ₁ (hypercoverPullTriangle pull comp ht) (hypercoverPullTriangle pull comp hs)
    hn₀ hn₁ ε₀ ε₁ α ht₀ ht₁

/-- Transport of a naturality square along an isomorphism `ν : N ≅ K`: if `t` and a natural
transformation `τ : r₀ ⋙ L ⟶ r₁` commute with `e₀, e₁` at `K`, they commute with `e₀ ≫ r₀ ν⁻¹` and
`e₁ ≫ r₁ ν⁻¹` at `N`. -/
theorem comp_map_inv_naturality {𝒦 : Type*} [Category 𝒦] (L : 𝒞₀ ⥤ 𝒞₁) (r₀ : 𝒦 ⥤ 𝒞₀)
    (r₁ : 𝒦 ⥤ 𝒞₁) (τ : r₀ ⋙ L ⟶ r₁) {K N : 𝒦} (ν : N ≅ K) {T₀ : 𝒞₀} {T₁ : 𝒞₁}
    (t : L.obj T₀ ⟶ T₁) (e₀ : T₀ ⟶ r₀.obj K) (e₁ : T₁ ⟶ r₁.obj K)
    (hn : t ≫ e₁ = L.map e₀ ≫ τ.app K) :
    t ≫ e₁ ≫ r₁.map ν.inv = L.map (e₀ ≫ r₀.map ν.inv) ≫ τ.app N := by
  have h := τ.naturality ν.inv
  simp only [Functor.comp_map] at h
  rw [reassoc_of% hn, ← h, L.map_comp, Category.assoc]

end CategoryTheory

/-! ### The four statements about the strict components -/

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Strict

variable (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The realization `R_n : D(𝒪_n) ⥤ D(𝒪_{X_n})` of the degree-`n` component of the strict
components of `X` on the spaces-étale site of `X_n`: the derived pullback along
`strictComponentRingedToposHom`, an equivalence. -/
abbrev strictComponentDerivedRealize (n : SimplexCategory) :=
  derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
    (strictComponentRingedToposHom X n)

/-- **Stacks 0GMF on the strict components, realized** (internal, pending). A pair `(K₀, α)` on
the spaces-étale sites of `X_0` and `X_1` satisfying the cocycle condition comes from a pair of
Stacks 0GMF on the strict components: the system of that pair realizes in degree `0` to `K₀` (by
`ε₀`) and in degree `1` to `Lδ₀^*K₀` (by `ε₁`), its transition along `δ₀` realizes to the
identity and its transition along `δ₁` to `α`, and in every degree `k` it realizes to the
pullback of `K₀` along the last vertex. The content is the pseudonaturality of the realizations
`R_n` (`strictComponentDerivedTransitionIso`) against the composition isomorphisms of derived
pullbacks on both sides (Stacks 0D6D). -/
def StrictPairRealization : Prop :=
  ∀ (K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0))))
    (α : (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).obj K₀ ≅
      (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).obj K₀),
    @IsHypercoverDescentCocycle _ _ (spacesEtaleDerivedModules B S hS) (fun _ => inferInstance)
      (fun f => spacesEtaleDerivedPull B S hS f)
      (fun f g => spacesEtaleDerivedPullComp B S hS f g) _ _ _ (X.δ (1 : Fin 2)) (X.δ (0 : Fin 2))
      (X.δ (2 : Fin 3)) (X.δ (0 : Fin 3)) (X.δ (1 : Fin 3)) _ α →
    ∃ (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
      (ε₀ : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj
        (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj
          (SimplexCategory.mk 0)) ≅ K₀)
      (ε₁ : (strictComponentDerivedRealize X (SimplexCategory.mk 1)).obj
        (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj
          (SimplexCategory.mk 1)) ≅ (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).obj K₀),
      (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).map
            (SimplexCategory.δ (0 : Fin 2))) =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).hom.app _ ≫
          (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).map ε₀.hom ≫ ε₁.inv ∧
      (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).map
            (SimplexCategory.δ (1 : Fin 2))) =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app _ ≫
          (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).map ε₀.hom ≫ α.hom ≫ ε₁.inv ∧
      ∀ k : ℕ, Nonempty ((strictComponentDerivedRealize X (SimplexCategory.mk k)).obj
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj
            (SimplexCategory.mk k)) ≅
        (spacesEtaleDerivedPull B S hS (X.map (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk k) (Fin.last k)).op)).obj K₀)

/-- **The derived transitions of a pullback along an augmentation, realized** (internal,
pending; Stacks 0D7H (4) made explicit). For an augmentation `a : X ⟶ Z` and `b = a ∘ e⁻¹` its
reading on the strict total site, the derived transition `Lf_φ^*(Lb^*M)_m ⟶ (Lb^*M)_n` realizes,
through `strictComponentDerivedTransitionIso` and `strictAugmentationDegreeDerivedIso`, to the
composition isomorphism `La_n^*M ≅ LX(φ)^* La_m^*M` of Stacks 0D6D. -/
def StrictAugmentationTransitionCoherent {Z : AlgebraicSpaces B S hS}
    (a : X ⟶ (Functor.const _).obj Z) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n) (hk : X.map φ.op ≫ a.app (op m) = a.app (op n))
    (M : spacesEtaleDerivedModules B S hS Z),
    @IsRealizedHypercoverTriangle _ _ _ _ (AlgebraicSpaces B S hS) _
      (spacesEtaleDerivedModules B S hS) (fun _ => inferInstance)
      (fun f => spacesEtaleDerivedPull B S hS f)
      (fun f g => spacesEtaleDerivedPullComp B S hS f g) _ _ _ (a.app (op m)) (X.map φ.op)
      (a.app (op n)) hk ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) φ)
      (strictComponentDerivedRealize X m) (strictComponentDerivedRealize X n)
      (strictComponentDerivedTransitionIso X φ) _ _
      (((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ).app
        ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj M)) M
      ((strictAugmentationDegreeDerivedIso a m).app M)
      ((strictAugmentationDegreeDerivedIso a n).app M)

end Strict

variable (B S hS) in
/-- **Quasi-coherence of a cartesian object of the strict total site** (internal, pending;
Stacks 0D7L (2) and 0D7M). For an fppf hypercovering `U`, a cartesian object `K` of the derived
category of the total site of the strict components of `U` whose components realize to complexes
with quasi-coherent cohomology on the `U_{n, spaces, étale}` has quasi-coherent cohomology on
`U_{spaces, étale}` after the comparison `e`. The face transitions are flat (Stacks 0DER), so the
cohomology sheaves of `K` are cartesian, and a cartesian module with quasi-coherent components is
quasi-coherent. -/
def StrictCartesianQuasicoherent : Prop :=
  ∀ (U : SimplicialObject.Augmented (AlgebraicSpaces B S hS)),
    IsHypercoveringAugmentation (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology
      U.left U.hom →
    ∀ K : DerivedCategory (strictRingedTopos U.left).Modules,
      (strictSituation U.left).IsCartesianDerivedModule (strictStructureSheaf U.left) K →
      (∀ n : SimplexCategory, IsSpacesEtaleQuasicoherentComplex B S hS (U.left.obj (op n))
        ((strictComponentDerivedRealize U.left n).obj
          (((strictSituation U.left).derivedComponentModuleRestriction
            (strictStructureSheaf U.left) n).obj K))) →
      (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U.left).O)))
        ((derivedPullback (X := ringedTopos U.left) (Y := strictRingedTopos U.left)
          (strictRingedToposHom U.left)).obj K)

variable (B S hS) in
/-- **Pullback along a vertex of an fppf hypercovering preserves quasi-coherence** (internal,
pending). The vertex `U_k ⟶ U_0` of an fppf hypercovering is flat (Stacks 0DER), so the derived
pullback along it of a complex with quasi-coherent cohomology has quasi-coherent cohomology. -/
def SpacesEtaleVertexQuasicoherent : Prop :=
  ∀ (U : SimplicialObject.Augmented (AlgebraicSpaces B S hS)),
    IsHypercoveringAugmentation (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology
      U.left U.hom →
    ∀ K₀ : spacesEtaleDerivedModules B S hS (U.left.obj (op (SimplexCategory.mk 0))),
      IsSpacesEtaleQuasicoherentComplex B S hS _ K₀ → ∀ k : ℕ,
      IsSpacesEtaleQuasicoherentComplex B S hS _
        ((spacesEtaleDerivedPull B S hS (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk k) (Fin.last k)).op)).obj K₀)

/-- Having quasi-coherent cohomology is invariant under isomorphism. -/
theorem isSpacesEtaleQuasicoherentComplex_of_iso {X : AlgebraicSpaces B S hS}
    {E E' : spacesEtaleDerivedModules B S hS X} (e : E ≅ E')
    (h : IsSpacesEtaleQuasicoherentComplex B S hS X E) :
    IsSpacesEtaleQuasicoherentComplex B S hS X E' :=
  fun n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).mapIso e) (h n)

variable (B S hS) in
/-- **Stacks 0DLA on the spaces-étale sites from Stacks 0D9T without flatness, through the
strict components.** Given the four statements about the strict components, P-core gives Stacks
0DLA on the spaces-étale sites. The proof is the source's: the pair `(K₀, α)` comes from a pair
of Stacks 0GMF on the strict components (`StrictPairRealization`), whose system P-core realizes as
a cartesian object `K`; its comparison with `U_{spaces,étale}` has quasi-coherent cohomology
(`StrictCartesianQuasicoherent`, `SpacesEtaleVertexQuasicoherent`), so by Stacks 0DHF it is
`La^*K'` for some `K'` with quasi-coherent cohomology; then `Lb^*K' ≅ K`, `β` is read off in
degree zero through `strictAugmentationDegreeDerivedIso`, and its compatibility with `α` is the
degree-one chase `CategoryTheory.isHypercoverDescentCompatible_of_strict`, whose input is
`StrictAugmentationTransitionCoherent`. -/
theorem spacesEtaleHypercoverDescentOfRealization_of_strict
    (h1 : ∀ X : SimplicialObject (AlgebraicSpaces B S hS), StrictPairRealization X)
    (h2 : ∀ (X : SimplicialObject (AlgebraicSpaces B S hS)) (Z : AlgebraicSpaces B S hS)
      (a : X ⟶ (Functor.const _).obj Z), StrictAugmentationTransitionCoherent X a)
    (h3 : StrictCartesianQuasicoherent B S hS) (h4 : SpacesEtaleVertexQuasicoherent B S hS) :
    SpacesEtaleHypercoverDescentOfRealization B S hS := by
  intro hcore U hU K₀ α hcoc hQ hExt
  obtain ⟨Pr, ε₀, ε₁, hT₀, hT₁, hεk⟩ := h1 U.left K₀ α hcoc
  have hExt' : ∀ (k : SimplexCategory) (t : ℤ), t < 0 →
      Subsingleton ((((strictSituation U.left).pairDerivedModuleSystem
          (strictStructureSheaf U.left) Pr).obj k) ⟶
        (shiftFunctor (DerivedCategory ((strictSituation U.left).componentRingedTopos
          (strictStructureSheaf U.left) k).Modules) t).obj
          (((strictSituation U.left).pairDerivedModuleSystem (strictStructureSheaf U.left) Pr).obj
            k)) := by
    intro k t ht
    obtain ⟨ι⟩ := hεk k.len
    have := hExt k.len t ht
    have : (strictComponentDerivedRealize U.left k).CommShift ℤ :=
      derivedPullback_commShift (strictComponentRingedToposHom U.left k)
    refine ⟨fun g g' => (strictComponentDerivedRealize U.left k).map_injective ?_⟩
    have hgg := Subsingleton.elim
      (ι.inv ≫ (strictComponentDerivedRealize U.left k).map g ≫
        ((strictComponentDerivedRealize U.left k).commShiftIso t).hom.app _ ≫
        (shiftFunctor _ t).map ι.hom)
      (ι.inv ≫ (strictComponentDerivedRealize U.left k).map g' ≫
        ((strictComponentDerivedRealize U.left k).commShiftIso t).hom.app _ ≫
        (shiftFunctor _ t).map ι.hom)
    have h2' := (cancel_epi ι.inv).1 hgg
    simp only [← Category.assoc] at h2'
    exact (cancel_mono _).1 ((cancel_mono _).1 h2')
  obtain ⟨K, hK, ⟨e⟩⟩ := (hcore (strictSituation U.left)
    (strictStructureSheaf U.left)).exists_of_subsingleton _
    ((strictSituation U.left).pairDerivedModuleSystem_cartesian (strictStructureSheaf U.left) Pr)
    hExt'
  have hQK := h3 U hU K hK fun n => by
    obtain ⟨ι⟩ := hεk n.len
    exact isSpacesEtaleQuasicoherentComplex_of_iso
      (ι.symm ≪≫ (strictComponentDerivedRealize U.left n).mapIso
        ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso e))
      (h4 U hU K₀ hQ n.len)
  obtain ⟨K', hK', ⟨γ⟩⟩ := exists_derivedPullback_obj_iso (T := bigFppfSpaceSiteOfSchemeSite B S hS)
    hU _ hQK
  obtain ⟨ν⟩ : Nonempty (((derivedPullback (X := strictRingedTopos U.left)
            (Y := spacesEtaleRingedTopos B S hS U.right)
            (strictAugmentationRingedToposHom U.hom)).obj K') ≅ K) := by
    have := hasLeftDerivedFunctor_pullbackOnHomotopy
      (RingedToposHom.comp (X := ringedTopos U.left) (Y := strictRingedTopos U.left)
          (Z := spacesEtaleRingedTopos B S hS U.right) (strictAugmentationRingedToposHom U.hom)
          (strictRingedToposHom U.left))
    exact ⟨(Functor.FullyFaithful.ofFullyFaithful (derivedPullback (X := ringedTopos U.left)
      (Y := strictRingedTopos U.left) (strictRingedToposHom U.left))).preimageIso
      ((derivedPullbackCompIso (strictRingedToposHom U.left)
          (strictAugmentationRingedToposHom U.hom) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := ringedTopos U.left) (Y := strictRingedTopos U.left)
            (Z := spacesEtaleRingedTopos B S hS U.right) (strictAugmentationRingedToposHom U.hom)
            (strictRingedToposHom U.left))
          (ψ := augmentationRingedToposHom U.hom)
          (strictAugmentationTwoIso U.hom).pullbackModulesIso).app K' ≪≫ γ)⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ∀ n : SimplexCategory,
      ((strictSituation U.left).pairDerivedModuleSystem (strictStructureSheaf U.left) Pr).obj n ≅
        ((strictSituation U.left).derivedComponentModuleRestriction (strictStructureSheaf U.left)
          n).obj ((derivedPullback (X := strictRingedTopos U.left)
            (Y := spacesEtaleRingedTopos B S hS U.right)
            (strictAugmentationRingedToposHom U.hom)).obj K'),
      ∀ i : Fin 2,
      ((strictSituation U.left).pairDerivedModuleSystem (strictStructureSheaf U.left) Pr).map
          (SimplexCategory.δ i) ≫ (ρ (SimplexCategory.mk 1)).hom =
        ((strictSituation U.left).derivedTransitionPullback (strictStructureSheaf U.left)
          (SimplexCategory.δ i)).map (ρ (SimplexCategory.mk 0)).hom ≫
          ((strictSituation U.left).derivedComponentModuleTransition (strictStructureSheaf U.left)
            (SimplexCategory.δ i)).app ((derivedPullback (X := strictRingedTopos U.left)
            (Y := spacesEtaleRingedTopos B S hS U.right)
            (strictAugmentationRingedToposHom U.hom)).obj K') :=
    ⟨fun n => (SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso e ≪≫
      ((strictSituation U.left).derivedComponentModuleRestriction (strictStructureSheaf U.left)
        n).mapIso ν.symm, fun i => comp_map_inv_naturality _ _ _
      ((strictSituation U.left).derivedComponentModuleTransition (strictStructureSheaf U.left)
        (SimplexCategory.δ i)) ν _ (e.hom.app _) (e.hom.app _)
      (e.hom.naturality (SimplexCategory.δ i))⟩
  have hδ : ∀ i : Fin 2, U.left.δ i ≫ U.hom.app (op (SimplexCategory.mk 0)) =
      U.hom.app (op (SimplexCategory.mk 1)) := fun i =>
    (U.hom.naturality (SimplexCategory.δ i).op).trans (Category.comp_id _)
  refine ⟨K', _, hK', isHypercoverDescentCompatible_of_strict _ _ _ _ _ _ (hδ 1) (hδ 0)
    ((strictSituation U.left).derivedTransitionPullback (strictStructureSheaf U.left)
      (SimplexCategory.δ (0 : Fin 2)))
    ((strictSituation U.left).derivedTransitionPullback (strictStructureSheaf U.left)
      (SimplexCategory.δ (1 : Fin 2)))
    (strictComponentDerivedRealize U.left (SimplexCategory.mk 0))
    (strictComponentDerivedRealize U.left (SimplexCategory.mk 1))
    (strictComponentDerivedTransitionIso U.left (SimplexCategory.δ (0 : Fin 2)))
    (strictComponentDerivedTransitionIso U.left (SimplexCategory.δ (1 : Fin 2)))
    K' _ _ _ _ (ρ (SimplexCategory.mk 0)) (ρ (SimplexCategory.mk 1)) (hρ 0) (hρ 1)
    ((strictAugmentationDegreeDerivedIso U.hom (SimplexCategory.mk 0)).app K')
    ((strictAugmentationDegreeDerivedIso U.hom (SimplexCategory.mk 1)).app K')
    ?_ ?_ ε₀ ε₁ α hT₀ hT₁⟩
  all_goals
    exact h2 U.left U.right U.hom (m := SimplexCategory.mk 0) (n := SimplexCategory.mk 1)
      (SimplexCategory.δ _) (by exact hδ _) K'

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
