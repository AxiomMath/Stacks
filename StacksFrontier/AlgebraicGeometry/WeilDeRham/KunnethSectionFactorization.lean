module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethSpaceFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StructureSheafRetraction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard

/-!
# Classes on `W` that agree along a section of `X ⟶ Spec A`

Let `f : X ⟶ S = Spec A` be proper and smooth with `Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)` an isomorphism, let
`σ` be a section of `f`, let `q, p : W ⟶ X` be two morphisms over `S`, and let `j : X ⟶ W`
satisfy `j ≫ q = 𝟙` and `j ≫ p = f ≫ σ`. Write `A' = Γ(S, 𝒪_S)`. For `K` in `D(𝒪_X)`, `n ≥ 0`
and `t : 𝒪_X[-n] ⟶ M` with `RΓ(X, M)` concentrated in degrees `≤ n`, two classes
`y, y'` of `RΓ(W, Lq^*K ⊗^𝐋 Lp^*𝒪_X[-n])` with `j^*y = j^*y'` satisfy
`(1 ⊗ Lp^*t)(y) = (1 ⊗ Lp^*t)(y')`, provided the global Künneth maps
`RΓ(X, K) ⊗^𝐋_{A'} RΓ(X, 𝒪_X[-n]) ⟶ RΓ(W, Lq^*K ⊗^𝐋 Lp^*𝒪_X[-n])` and
`RΓ(X, K) ⊗^𝐋_{A'} RΓ(S, 𝒪_S[-n]) ⟶ RΓ(X, K ⊗^𝐋 Lf^*𝒪_S[-n])` are invertible. This is the step
of the proof of [Stacks, Tag 0G8J] identifying the two maps called `θ₁` and `θ` there.

The proof is the source's. Write `y = κ_W(d)` with `κ_W` the first Künneth map. By naturality of
the Künneth map in the second variable, `(1 ⊗ Lp^*t)(y)` is the image of `(1 ⊗ RΓ(t))(d)`. Let
`s : RΓ(X, 𝒪_X[-n]) ⟶ A'[-n]` be the pullback along `σ` followed by `Lσ^*𝒪_X[-n] ≅ 𝒪_S[-n]`
and `RΓ(S, 𝒪_S[-n]) ≅ A'[-n]`; it has a right inverse `u`, built from the pullback along `f`,
because the pullback along `σ ≫ f = 𝟙` is invertible. The vanishing
`Stacks.WeilDeRham.retractionVanishing_single` gives `RΓ(t) = s ≫ u ≫ RΓ(t)`, so it suffices that
`(1 ⊗ s)(d) = (1 ⊗ s)(d')`. Pulling back along `j` turns `κ_W` into the Künneth map for the
projections `(j ≫ q, j ≫ p) = (𝟙, f ≫ σ)`, which is `1 ⊗ σ^*` followed by the second, invertible,
Künneth map; so `j^*y = j^*y'` forces `(1 ⊗ σ^*)(d) = (1 ⊗ σ^*)(d')`, and hence the claim.

## Main definitions

* `Stacks.WeilDeRham.unitInDegree`: the structure sheaf placed in degree `n`.
* `Stacks.WeilDeRham.KunnethSectionFactorization`: the statement above.

## Main results

* `Stacks.WeilDeRham.kunnethSectionFactorization`: the statement holds under the two Künneth
  isomorphisms.
* `Stacks.WeilDeRham.homology_map_tensor_eq_of_pullbackSections_eq`: the same argument for
  morphisms of ringed spaces, with the vanishing and the identifications of the structure
  sheaves as hypotheses.
* `Stacks.WeilDeRham.exists_comp_pullbackSections_section_eq_id`: the pullback along a section,
  followed by an isomorphism, has a right inverse.
* `Stacks.WeilDeRham.nonempty_sectionsOverBase_unitInDegree_iso`:
  `RΓ(Spec A, 𝒪[-n]) ≅ Γ(Spec A, 𝒪)[-n]`.
* `Stacks.WeilDeRham.isIso_kunnethGlobalMapCanonical_of_iso_right`: invertibility of the global
  Künneth map depends on the second complex only up to isomorphism.

## Implementation notes

The two Künneth isomorphisms are hypotheses: they are instances of [Stacks, Tag 0FLQ] at the
fibre products `W ≅ X ×_S X` and `X = X ×_S S`, and are stated in the form in which the global
Künneth map at two shifted flat quasi-coherent modules is shown invertible, for `K` such a
module. The second one is stated at `𝒪_S[-n]` with the identity of `S`, rather than at
`Lσ^*𝒪_X[-n]` over `σ ≫ f`, and is transported along `Lσ^*𝒪_X[-n] ≅ 𝒪_S[-n]` and `σ ≫ f = 𝟙`.

The isomorphism `RΓ(Spec A, 𝒪[-n]) ≅ Γ(Spec A, 𝒪)[-n]` is only asserted to exist: the argument
uses no property of the retraction beyond `u ≫ s = 𝟙`.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.KunnethCupWithClass (pullbackSections)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

/-! ### Elementwise bookkeeping -/

section Elementwise

variable {C : Type*} [Category C] {R : Type u} [Ring R] (H : C ⥤ ModuleCat.{u} R)

/-- Two factorizations of one morphism agree elementwise after applying `H`. -/
private theorem map_hom_apply_eq_of_comp_eq {P Q Q' Z : C} (x : P ⟶ Q) (y : Q ⟶ Z) (x' : P ⟶ Q')
    (y' : Q' ⟶ Z) (h : x ≫ y = x' ≫ y') (z : H.obj P) :
    (H.map y).hom ((H.map x).hom z) = (H.map y').hom ((H.map x').hom z) := by
  simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun g => (H.map g).hom z) h

/-- `H` of a composite, on elements. -/
theorem map_comp_hom_apply {P Q Z : C} (x : P ⟶ Q) (y : Q ⟶ Z) (z : H.obj P) :
    (H.map (x ≫ y)).hom z = (H.map y).hom ((H.map x).hom z) := by
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- Two elements identified by `H x` are identified by `H (x ≫ y)`. -/
private theorem map_hom_eq_of_comp_eq {P Q Z : C} (x : P ⟶ Q) (y : Q ⟶ Z) (w : P ⟶ Z)
    (h : x ≫ y = w) {z z' : H.obj P} (hz : (H.map x).hom z = (H.map x).hom z') :
    (H.map w).hom z = (H.map w).hom z' := by
  subst h
  rw [map_comp_hom_apply, map_comp_hom_apply, hz]

/-- `H` of an isomorphism is injective on elements. -/
private theorem map_hom_injective_of_isIso {P Q : C} (x : P ⟶ Q) [IsIso x] :
    Function.Injective (H.map x).hom :=
  (ConcreteCategory.bijective_of_isIso (H.map x)).1

/-- Two elements identified by `H (x ≫ y)`, for `y` invertible, are identified by `H x`. -/
private theorem map_hom_eq_of_comp_eq_of_isIso {P Q Z : C} (x : P ⟶ Q) (y : Q ⟶ Z) (w : P ⟶ Z)
    (hy : IsIso y) (h : x ≫ y = w) {z z' : H.obj P} (hz : (H.map w).hom z = (H.map w).hom z') :
    (H.map x).hom z = (H.map x).hom z' := by
  subst h
  rw [map_comp_hom_apply, map_comp_hom_apply] at hz
  exact map_hom_injective_of_isIso H y hz

/-- `H` of an isomorphism is surjective on elements. -/
private theorem map_hom_surjective_of_isIso {P Q : C} (x : P ⟶ Q) [IsIso x] :
    Function.Surjective (H.map x).hom :=
  (ConcreteCategory.bijective_of_isIso (H.map x)).2

end Elementwise

/-! ### Bookkeeping for the global Künneth map -/

section Spaces

variable {S X Y W : RingedSpace.{u, u}}

/-- An isomorphism from a composite through a naturality square and a composition identity. -/
private theorem isIso_comp_of_naturality {C : Type*} [Category C] {P Q₁ Q₂ Z₁ Z₂ Z₁' T : C}
    (v : P ⟶ Q₁) (x : Q₁ ⟶ Q₂) (s : Q₂ ⟶ Z₁) (y : Z₁ ⟶ Z₂) (s' : Q₁ ⟶ Z₁') (n : Z₁' ⟶ Z₁)
    (c : Z₁' ⟶ T) (i : P ⟶ T) [IsIso c] [IsIso i] [IsIso n] [IsIso y]
    (hn : x ≫ s = s' ≫ n) (hc : v ≫ s' ≫ c = i) : IsIso (v ≫ x ≫ s ≫ y) := by
  have h : v ≫ x ≫ s ≫ y = i ≫ inv c ≫ n ≫ y := by
    rw [reassoc_of% hn, ← hc]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [h]
  infer_instance

/-- A morphism `S'` with `V ≫ S'` invertible, followed by an isomorphism `E`, has a right
inverse. -/
private theorem exists_comp_comp_hom_eq_id {C : Type*} [Category C] {N P Z : C} (E : Z ≅ N)
    (V : Z ⟶ P) (S' : P ⟶ Z) [IsIso (V ≫ S')] : ∃ u : N ⟶ P, u ≫ S' ≫ E.hom = 𝟙 N :=
  ⟨E.inv ≫ inv (V ≫ S') ≫ V, by
    rw [Category.assoc, Category.assoc, ← Category.assoc V, IsIso.inv_hom_id_assoc,
      Iso.inv_hom_id]⟩

/-- A functor sends the forward map of an isomorphism to an isomorphism. -/
private theorem isIso_map_hom {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P Q : C}
    (e : P ≅ Q) : IsIso (F.map e.hom) :=
  (F.mapIso e).isIso_hom

variable (a : X ⟶ S) (b : Y ⟶ S)

/-- The global Künneth map depends on its projections only through their values: for equal
projections the two maps identify the same pairs of classes. -/
theorem kunnethGlobalMapCanonical_homology_eq_iff {p₁ p₂ : W ⟶ X} {q₁ q₂ : W ⟶ Y}
    {f₁ f₂ : W ⟶ S} (hp₁ : p₁ ≫ a = f₁) (hq₁ : q₁ ≫ b = f₁) (hp₂ : p₂ ≫ a = f₂)
    (hq₂ : q₂ ≫ b = f₂) (hp : p₁ = p₂) (hq : q₁ = q₂)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (m : ℤ)
    (d d' : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).obj
      (((tensorBase S).obj ((sectionsOverBase a).obj K)).obj ((sectionsOverBase b).obj M))) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        (kunnethGlobalMapCanonical a b p₁ q₁ f₁ hp₁ hq₁ K M)).hom d =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        (kunnethGlobalMapCanonical a b p₁ q₁ f₁ hp₁ hq₁ K M)).hom d' ↔
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        (kunnethGlobalMapCanonical a b p₂ q₂ f₂ hp₂ hq₂ K M)).hom d =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        (kunnethGlobalMapCanonical a b p₂ q₂ f₂ hp₂ hq₂ K M)).hom d' := by
  subst hp hq hp₁ hp₂
  exact Iff.rfl

/-- Invertibility of the global Künneth map is unchanged when the structure morphisms and the
projections are replaced by equal ones. -/
theorem isIso_kunnethGlobalMapCanonical_of_eq {b₁ b₂ : Y ⟶ S} {p₁ p₂ : W ⟶ X}
    {q₁ q₂ : W ⟶ Y} {f₁ f₂ : W ⟶ S} (hb : b₁ = b₂) (hp : p₁ = p₂) (hq : q₁ = q₂)
    (hf : f₁ = f₂) (hp₁ : p₁ ≫ a = f₁) (hq₁ : q₁ ≫ b₁ = f₁) (hp₂ : p₂ ≫ a = f₂)
    (hq₂ : q₂ ≫ b₂ = f₂) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (kunnethGlobalMapCanonical a b₁ p₁ q₁ f₁ hp₁ hq₁ K M)) :
    IsIso (kunnethGlobalMapCanonical a b₂ p₂ q₂ f₂ hp₂ hq₂ K M) := by
  subst hb hp hq hf
  exact h

/-- Invertibility of the global Künneth map at `(K, M)` depends on `M` only up to
isomorphism. -/
theorem isIso_kunnethGlobalMapCanonical_of_iso_right (p : W ⟶ X) (q : W ⟶ Y) (f : W ⟶ S)
    (hp : p ≫ a = f) (hq : q ≫ b = f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (e : M ≅ M')
    (h : IsIso (kunnethGlobalMapCanonical a b p q f hp hq K M')) :
    IsIso (kunnethGlobalMapCanonical a b p q f hp hq K M) := by
  have hnat := kunnethGlobalMap_naturality_right a b p q f hp hq (globalCupProductCanonical S) K
    e.hom
  have h₁ := isIso_map_hom (sectionsOverBase f) (((derivedTensorProductFunctor W.sheaf).obj
    ((derivedPullback p).obj K)).mapIso ((derivedPullback q).mapIso e))
  have h₂ := isIso_map_hom ((tensorBase S).obj ((sectionsOverBase a).obj K))
    ((sectionsOverBase b).mapIso e)
  have h₃ := @IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ h₁ h₃ hnat.symm

end Spaces


/-- **A retraction through a section.** If `σ` is a section of `a : X ⟶ S`, and `O` on `X`,
`O_S` on `S` are identified by `Lσ^*O ≅ O_S` and `La^*O_S ≅ O`, then the pullback
`RΓ(X, O) ⟶ RΓ(S, Lσ^*O) ≅ RΓ(S, O_S)` along `σ`, followed by any isomorphism
`RΓ(S, O_S) ≅ N`, has a right inverse: the pullback along `a` is one up to the invertible
pullback along `σ ≫ a = 𝟙`. -/
theorem exists_comp_pullbackSections_section_eq_id {S X : RingedSpace.{u, u}} (a : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ a = 𝟙 S)
    (O : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (OS : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (N : DerivedCategory (ModuleCat.{u} (baseRing S)))
    (e : (derivedPullback σ).obj O ≅ OS) (ea : (derivedPullback a).obj OS ≅ O)
    (E : (sectionsOverBase (σ ≫ a)).obj OS ≅ N) :
    ∃ u : N ⟶ (sectionsOverBase a).obj O,
      u ≫ (pullbackSections a σ (σ ≫ a) rfl O ≫ (sectionsOverBase (σ ≫ a)).map e.hom) ≫
        E.hom = 𝟙 N := by
  have hva : a ≫ σ ≫ a = a := by rw [hσ, Category.comp_id]
  have hc := isIso_map_hom (sectionsOverBase (σ ≫ a))
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical σ a).app OS)
  have hσσ : (σ ≫ a) ≫ σ ≫ a = σ ≫ a := by rw [hσ, Category.comp_id]
  have hi : IsIso (pullbackSections (σ ≫ a) (σ ≫ a) (σ ≫ a) hσσ OS) :=
    isIso_pullbackSections_of_eq_id (σ ≫ a) (σ ≫ a) (σ ≫ a) hσσ hσ rfl OS
  have hn := isIso_map_hom (sectionsOverBase (σ ≫ a)) ((derivedPullback σ).mapIso ea)
  have hy := isIso_map_hom (sectionsOverBase (σ ≫ a)) e
  have hv := isIso_comp_of_naturality (pullbackSections (σ ≫ a) a a hva OS)
    ((sectionsOverBase a).map ea.hom) (pullbackSections a σ (σ ≫ a) rfl O)
    ((sectionsOverBase (σ ≫ a)).map e.hom)
    (pullbackSections a σ (σ ≫ a) rfl ((derivedPullback a).obj OS))
    ((sectionsOverBase (σ ≫ a)).map ((derivedPullback σ).map ea.hom))
    ((sectionsOverBase (σ ≫ a)).map
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical σ a).hom.app OS))
    (pullbackSections (σ ≫ a) (σ ≫ a) (σ ≫ a) hσσ OS)
    (pullbackSections_naturality a σ (σ ≫ a) rfl ea.hom)
    (pullbackSections_comp (σ ≫ a) a a hva σ OS)
  have : IsIso ((pullbackSections (σ ≫ a) a a hva OS ≫ (sectionsOverBase a).map ea.hom) ≫
      pullbackSections a σ (σ ≫ a) rfl O ≫ (sectionsOverBase (σ ≫ a)).map e.hom) := by
    rw [Category.assoc]
    exact hv
  exact exists_comp_comp_hom_eq_id E
    (pullbackSections (σ ≫ a) a a hva OS ≫ (sectionsOverBase a).map ea.hom) _

/-! ### The argument on ringed spaces -/

section Core

variable {S X W : RingedSpace.{u, u}}

/-- **The factorization through a section, on ringed spaces.** Let `a : X ⟶ S` have a section
`σ`, let `q, p : W ⟶ X` be two projections over `S` and `j : X ⟶ W` with `j ≫ q = 𝟙` and
`j ≫ p = a ≫ σ`. Let `O` on `X` and `O_S` on `S` be identified by `Lσ^*O ≅ O_S` and
`La^*O_S ≅ O`, and let `RΓ(S, O_S) ≅ N`. Assume the global Künneth maps through `W` at `(K, O)`
and through `X` at `(K, O_S)` are invertible, and that every retraction of `RΓ(X, O)` onto `N`
acts trivially on `RΓ(X, t)` for `t : O ⟶ M`. Then two classes of
`RΓ(W, Lq^*K ⊗^𝐋 Lp^*O)` with the same pullback along `j` have the same image under
`Lq^*K ⊗^𝐋 Lp^*t`. -/
theorem homology_map_tensor_eq_of_pullbackSections_eq (a : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ a = 𝟙 S) (q p : W ⟶ X) (g : W ⟶ S) (hq : q ≫ a = g) (hp : p ≫ a = g)
    (j : X ⟶ W) (g' : X ⟶ S) (hj : j ≫ g = g') (hjq : j ≫ q = 𝟙 X) (hjp : j ≫ p = a ≫ σ)
    (K O : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (OS : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (N : DerivedCategory (ModuleCat.{u} (baseRing S)))
    (e : (derivedPullback σ).obj O ≅ OS) (ea : (derivedPullback a).obj OS ≅ O)
    (E : (sectionsOverBase (σ ≫ a)).obj OS ≅ N)
    (hκW : IsIso (kunnethGlobalMapCanonical a a q p g hq hp K O))
    (hκX : IsIso (kunnethGlobalMapCanonical a (𝟙 S) (𝟙 X) a a (Category.id_comp a)
      (Category.comp_id a) K OS))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (t : O ⟶ M)
    (hvan : ∀ (u : N ⟶ (sectionsOverBase a).obj O) (s : (sectionsOverBase a).obj O ⟶ N),
      u ≫ s = 𝟙 _ → s ≫ u ≫ (sectionsOverBase a).map t = (sectionsOverBase a).map t)
    (m : ℤ)
    (y y' : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).obj
      ((sectionsOverBase g).obj (((derivedTensorProductFunctor W.sheaf).obj
        ((derivedPullback q).obj K)).obj ((derivedPullback p).obj O))))
    (hy : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        (pullbackSections g j g' hj (((derivedTensorProductFunctor W.sheaf).obj
          ((derivedPullback q).obj K)).obj ((derivedPullback p).obj O)))).hom y =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        (pullbackSections g j g' hj (((derivedTensorProductFunctor W.sheaf).obj
          ((derivedPullback q).obj K)).obj ((derivedPullback p).obj O)))).hom y') :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        ((sectionsOverBase g).map (((derivedTensorProductFunctor W.sheaf).obj
          ((derivedPullback q).obj K)).map ((derivedPullback p).map t)))).hom y =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
        ((sectionsOverBase g).map (((derivedTensorProductFunctor W.sheaf).obj
          ((derivedPullback q).obj K)).map ((derivedPullback p).map t)))).hom y' := by
  subst hj
  obtain ⟨d, hd⟩ := map_hom_surjective_of_isIso
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m)
    (kunnethGlobalMapCanonical a a q p g hq hp K O) y
  obtain ⟨d', hd'⟩ := map_hom_surjective_of_isIso
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m)
    (kunnethGlobalMapCanonical a a q p g hq hp K O) y'
  subst hd hd'
  have hnat : ((tensorBase S).obj ((sectionsOverBase a).obj K)).map ((sectionsOverBase a).map t) ≫
      kunnethGlobalMapCanonical a a q p g hq hp K M =
      kunnethGlobalMapCanonical a a q p g hq hp K O ≫
        (sectionsOverBase g).map (((derivedTensorProductFunctor W.sheaf).obj
          ((derivedPullback q).obj K)).map ((derivedPullback p).map t)) :=
    kunnethGlobalMap_naturality_right a a q p g hq hp (globalCupProductCanonical S) K t
  have h₁ := map_hom_apply_eq_of_comp_eq
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m) _ _ _ _ hnat d
  have h₂ := map_hom_apply_eq_of_comp_eq
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m) _ _ _ _ hnat d'
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  refine congrArg (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m).map
    (kunnethGlobalMapCanonical a a q p g hq hp K M)).hom) ?_
  -- the vanishing: `RΓ(X, t)` factors through the retraction
  have hex := exists_comp_pullbackSections_section_eq_id a σ hσ O OS N e ea E
  obtain ⟨u, hus⟩ := hex
  have hv := hvan u _ hus
  refine map_hom_eq_of_comp_eq (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m)
    (((tensorBase S).obj ((sectionsOverBase a).obj K)).map
      ((pullbackSections a σ (σ ≫ a) rfl O ≫ (sectionsOverBase (σ ≫ a)).map e.hom) ≫ E.hom))
    (((tensorBase S).obj ((sectionsOverBase a).obj K)).map (u ≫ (sectionsOverBase a).map t))
    (((tensorBase S).obj ((sectionsOverBase a).obj K)).map ((sectionsOverBase a).map t))
    (by rw [← Functor.map_comp, hv]) ?_
  refine map_hom_eq_of_comp_eq (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m)
    (((tensorBase S).obj ((sectionsOverBase a).obj K)).map
      (pullbackSections a σ (σ ≫ a) rfl O))
    (((tensorBase S).obj ((sectionsOverBase a).obj K)).map
      ((sectionsOverBase (σ ≫ a)).map e.hom ≫ E.hom))
    (((tensorBase S).obj ((sectionsOverBase a).obj K)).map
      ((pullbackSections a σ (σ ≫ a) rfl O ≫ (sectionsOverBase (σ ≫ a)).map e.hom) ≫ E.hom))
    (by rw [← Functor.map_comp, Category.assoc]) ?_
  -- restriction along `j`
  have hKP := kunnethGlobalMapCanonical_comp_pullbackSections a a q p g hq hp j K O
  have h₃ := map_hom_eq_of_comp_eq
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m) _ _ _
    ((Category.assoc _ _ _).trans hKP)
    ((map_comp_hom_apply _ _ _ d).trans (hy.trans (map_comp_hom_apply _ _ _ d').symm))
  have hq₂ : (a ≫ σ) ≫ a = a := by rw [Category.assoc, hσ, Category.comp_id]
  have hq' : a ≫ σ ≫ a = a := by rw [hσ, Category.comp_id]
  have h₄ := (kunnethGlobalMapCanonical_homology_eq_iff a a _ _ (Category.id_comp a) hq₂ hjq hjp
    K O m d d').1 h₃
  -- the Künneth map for `(𝟙, a ≫ σ)` through the pullback along `σ`
  have hpr := kunnethGlobalMapCanonical_precomp_right a a (𝟙 X) a (Category.id_comp a) σ a hq' K O
  have hκ' := isIso_kunnethGlobalMapCanonical_of_iso_right a (σ ≫ a) (𝟙 X) a a
    (Category.id_comp a) hq' K e
    (isIso_kunnethGlobalMapCanonical_of_eq a hσ.symm rfl rfl rfl (Category.id_comp a)
      (Category.comp_id a) (Category.id_comp a) hq' K OS hκX)
  have hR := isIso_map_hom (sectionsOverBase a) (((derivedTensorProductFunctor X.sheaf).obj
    ((derivedPullback (𝟙 X)).obj K)).mapIso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a σ).app O))
  have hcomp := @IsIso.comp_isIso _ _ _ _ _ _ _ hκ' hR
  exact map_hom_eq_of_comp_eq_of_isIso
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) m) _ _ _ hcomp hpr.symm h₄

end Core


/-! ### The affine base -/

section Affine

variable {A : Type u} [CommRing A]

/-- The structure sheaf placed in degree `n`. -/
abbrev unitInDegree (V : Scheme.{u}) (n : ℕ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing V.toRingedSpace)) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
    (n : ℤ)).obj (SheafOfModules.unit (structureSheafRing V.toRingedSpace))

/-- **`RΓ(Spec A, 𝒪[-n]) ≅ A'[-n]`** for `A' = Γ(Spec A, 𝒪)`, read through any endomorphism of
`Spec A` equal to the identity: after restriction of scalars along `A ≅ A'`, which is an
equivalence of derived categories, this is the unit `A[-n] ⟶ RΓ(Spec A, A[-n]^~)` of the derived
Spec–Γ adjunction, invertible by [Stacks, Tag 06Z0]. -/
theorem nonempty_sectionsOverBase_unitInDegree_iso
    (c : (Spec (.of A)).toRingedSpace ⟶ (Spec (.of A)).toRingedSpace) (hc : c = 𝟙 _) (n : ℕ) :
    Nonempty ((sectionsOverBase c).obj (unitInDegree (Spec (.of A)) n) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
        (n : ℤ)).obj (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
          (baseRing (Spec (.of A)).toRingedSpace))) := by
  subst hc
  let G := ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of A)).inv.hom
  let Φ := G.mapDerivedCategory
  have : G.IsEquivalence := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm).isEquivalence_functor
  have : Φ.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence G
  obtain ⟨eR⟩ := nonempty_derivedGlobalSectionsOver_iso_restrictScalars (𝟙 (Spec (.of A)))
    (unitInDegree (Spec (.of A)) n)
  let l : A →ₗ[A] G.obj (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
      (baseRing (Spec (.of A)).toRingedSpace)) :=
    { toFun := fun a => ((Scheme.ΓSpecIso (.of A)).inv.hom a :
        (baseRing (Spec (.of A)).toRingedSpace))
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a b => by
        show (Scheme.ΓSpecIso (.of A)).inv.hom (a * b) =
          (Scheme.ΓSpecIso (.of A)).inv.hom a * (Scheme.ΓSpecIso (.of A)).inv.hom b
        exact map_mul _ a b }
  have hl : Function.Bijective l :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv
  let e₁ : Φ.obj ((DerivedCategory.singleFunctor _ (n : ℤ)).obj
      (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
        (baseRing (Spec (.of A)).toRingedSpace))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj (ModuleCat.of A A) :=
    (G.mapDerivedCategorySingleFunctor (n : ℤ)).app _ ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).mapIso
        (LinearEquiv.ofBijective l hl).toModuleIso.symm
  have := AlgebraicGeometry.StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit
    (CommRingCat.of A)
  let eT := asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A)).val.unit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj (ModuleCat.of A A)))
  let eS : (tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj (ModuleCat.of A A)) ≅
      unitInDegree (Spec (.of A)) n :=
    ((tilde.functor (CommRingCat.of A)).mapDerivedCategorySingleFunctor (n : ℤ)).app
        (ModuleCat.of A A) ≪≫
      (DerivedCategory.singleFunctor _ (n : ℤ)).mapIso tildeSelf
  exact ⟨Φ.preimageIso (eR.symm ≪≫ (derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).mapIso eS.symm ≪≫
    eT.symm ≪≫ e₁.symm)⟩

end Affine

/-! ### The factorization through the section -/

section Factorization

variable {A : Type u} [CommRing A] {X W : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The factorization through the section.** For `q, p : W ⟶ X` over `S = Spec A`, a section
`σ` of `f` and `j : X ⟶ W`, the statement that two classes `y, y'` of
`RΓ(W, Lq^*K ⊗^𝐋 Lp^*𝒪_X[-n])` in degree `m` with the same pullback along `j` have the same
image under `Lq^*K ⊗^𝐋 Lp^*t`, for every `t : 𝒪_X[-n] ⟶ M` with `RΓ(X, M)` concentrated in
degrees `≤ n`. -/
def KunnethSectionFactorization (σ : Spec (.of A) ⟶ X) (q p : W ⟶ X) (hqp : q ≫ f = p ≫ f)
    (j : X ⟶ W) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (n : ℕ) : Prop :=
  ∀ (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    [((sectionsOverBase f.toLRSHom.toShHom).obj M).IsLE (n : ℤ)]
    (t : unitInDegree X n ⟶ M) (m : ℤ)
    (y y' : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
        m).obj ((sectionsOverBase (q ≫ f).toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj
            ((derivedPullback q.toLRSHom.toShHom).obj K)).obj
            ((derivedPullback p.toLRSHom.toShHom).obj (unitInDegree X n))))),
    ((DerivedCategory.homologyFunctor _ m).map
        (pullbackSections (q ≫ f).toLRSHom.toShHom j.toLRSHom.toShHom
          (j ≫ q ≫ f).toLRSHom.toShHom rfl _)).hom y =
      ((DerivedCategory.homologyFunctor _ m).map
        (pullbackSections (q ≫ f).toLRSHom.toShHom j.toLRSHom.toShHom
          (j ≫ q ≫ f).toLRSHom.toShHom rfl _)).hom y' →
    ((DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase (q ≫ f).toLRSHom.toShHom).map
        (((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj
          ((derivedPullback q.toLRSHom.toShHom).obj K)).map
          ((derivedPullback p.toLRSHom.toShHom).map t)))).hom y =
      ((DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase (q ≫ f).toLRSHom.toShHom).map
        (((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj
          ((derivedPullback q.toLRSHom.toShHom).obj K)).map
          ((derivedPullback p.toLRSHom.toShHom).map t)))).hom y'

/-- **The factorization through the section holds** for `f : X ⟶ Spec A` proper and smooth with
`Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` invertible, a section `σ` of `f`, and `j : X ⟶ W` with
`j ≫ q = 𝟙` and `j ≫ p = f ≫ σ`, as soon as the global Künneth maps through `W` at
`(K, 𝒪_X[-n])` and through `X = X ×_S S` at `(K, 𝒪_S[-n])` are invertible. -/
theorem kunnethSectionFactorization [IsProper f] [Smooth f] [IsIso f.appTop]
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (q p : W ⟶ X) (hqp : q ≫ f = p ≫ f)
    (j : X ⟶ W) (hjq : j ≫ q = 𝟙 X) (hjp : j ≫ p = f ≫ σ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (n : ℕ)
    (hκW : IsIso (kunnethGlobalMapCanonical f.toLRSHom.toShHom f.toLRSHom.toShHom
      q.toLRSHom.toShHom p.toLRSHom.toShHom (q ≫ f).toLRSHom.toShHom rfl
      (by rw [hqp]; rfl) K (unitInDegree X n)))
    (hκX : IsIso (kunnethGlobalMapCanonical f.toLRSHom.toShHom
      (𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)).toLRSHom.toShHom
      (𝟙 X : X ⟶ X).toLRSHom.toShHom f.toLRSHom.toShHom
      (𝟙 X ≫ f).toLRSHom.toShHom rfl (by rw [Category.id_comp]; exact Category.comp_id _) K
      (unitInDegree (Spec (.of A)) n))) :
    KunnethSectionFactorization f σ q p hqp j K n := by
  intro M _ t m y y' hy
  have hσ' : σ.toLRSHom.toShHom ≫ f.toLRSHom.toShHom = 𝟙 _ :=
    congrArg (fun g => g.toLRSHom.toShHom) hσ
  have hjq' : j.toLRSHom.toShHom ≫ q.toLRSHom.toShHom = 𝟙 _ :=
    congrArg (fun g => g.toLRSHom.toShHom) hjq
  have hjp' : j.toLRSHom.toShHom ≫ p.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ σ.toLRSHom.toShHom :=
    congrArg (fun g => g.toLRSHom.toShHom) hjp
  have hf' : (𝟙 X ≫ f).toLRSHom.toShHom = f.toLRSHom.toShHom :=
    congrArg (fun g => g.toLRSHom.toShHom) (Category.id_comp f)
  obtain ⟨E⟩ := nonempty_sectionsOverBase_unitInDegree_iso
    (σ.toLRSHom.toShHom ≫ f.toLRSHom.toShHom) hσ' n
  have hκX' : IsIso (kunnethGlobalMapCanonical f.toLRSHom.toShHom (𝟙 _) (𝟙 _)
      f.toLRSHom.toShHom f.toLRSHom.toShHom (Category.id_comp _) (Category.comp_id _) K
      (unitInDegree (Spec (.of A)) n)) :=
    isIso_kunnethGlobalMapCanonical_of_eq f.toLRSHom.toShHom rfl rfl rfl hf' _ _ _ _ K _ hκX
  have hvan : ∀ (u : (DerivedCategory.singleFunctor _ (n : ℤ)).obj
        (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
          (baseRing (Spec (.of A)).toRingedSpace)) ⟶
        (sectionsOverBase f.toLRSHom.toShHom).obj (unitInDegree X n))
      (s : (sectionsOverBase f.toLRSHom.toShHom).obj (unitInDegree X n) ⟶
        (DerivedCategory.singleFunctor _ (n : ℤ)).obj
          (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
            (baseRing (Spec (.of A)).toRingedSpace))),
      u ≫ s = 𝟙 _ → s ≫ u ≫ (sectionsOverBase f.toLRSHom.toShHom).map t =
        (sectionsOverBase f.toLRSHom.toShHom).map t :=
    fun u s hus => retractionVanishing_single f n u s hus _ _
  exact homology_map_tensor_eq_of_pullbackSections_eq f.toLRSHom.toShHom σ.toLRSHom.toShHom hσ'
    q.toLRSHom.toShHom p.toLRSHom.toShHom (q ≫ f).toLRSHom.toShHom rfl (by rw [hqp]; rfl)
    j.toLRSHom.toShHom (j ≫ q ≫ f).toLRSHom.toShHom rfl hjq' hjp' K (unitInDegree X n)
    (unitInDegree (Spec (.of A)) n) _
    (Stacks.RingedSpace.derivedPullbackShiftedUnitIso σ.toLRSHom.toShHom n)
    (Stacks.RingedSpace.derivedPullbackShiftedUnitIso f.toLRSHom.toShHom n) E hκW hκX' M t hvan
    m y y' hy

end Factorization

end Stacks.WeilDeRham

end
