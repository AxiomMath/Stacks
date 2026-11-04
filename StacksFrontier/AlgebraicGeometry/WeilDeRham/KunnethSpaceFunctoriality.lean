module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethCupWithClassCanonical
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.UnitAlongAComposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Functoriality of the pullback on derived global sections and of the global Künneth map

Let `a : X ⟶ S` be a morphism of ringed spaces and `A = Γ(S, 𝒪_S)`. For `p : W ⟶ X` with
`p ≫ a = f`, the pullback map `p^* : RΓ(X, K) ⟶ RΓ(W, Lp^*K)` in `D(A)` used in Equation
36.23.0.2 is `RΓ(S, -)` of the adjoint `Ra_*K ⟶ Rf_*Lp^*K` of the counit leg, read through the
Leray isomorphisms. That adjoint is `Ra_*` of the unit of `Lp^* ⊣ Rp_*` followed by the
composition isomorphism `Ra_* Rp_* ≅ R(p ≫ a)_*` of derived pushforward, so the compatibility of
the units with composition makes `p^*` functorial: for `g : W' ⟶ W` the composite `g^* ∘ p^*`,
read through the composition isomorphism `Lg^*Lp^* ≅ L(g ≫ p)^*`, is `(g ≫ p)^*`, and `(𝟙 X)^*`
is the identity, read through `L(𝟙 X)^* ≅ 𝟭`.

Two properties of the global Künneth map
`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋 Lq^*M)` follow, since it is the two pullback maps
followed by the cup product on `W`. It is compatible with pullback along `g : W' ⟶ W`, by the
compatibility of the cup products with pullback and the functoriality of `p^*` and `q^*`. And
when a projection factors as `p' ≫ h`, it factors through the pullback along `h` in that
variable. Finally `p^*` is natural, and invertible when `p` is an isomorphism.

## Main results

* `Stacks.WeilDeRham.pullbackSections_comp`: `g^* ∘ p^* = (g ≫ p)^*`.
* `Stacks.WeilDeRham.pullbackSections_id`: `(𝟙 X)^*` is the identity.
* `Stacks.WeilDeRham.kunnethGlobalMapCanonical_comp_pullbackSections`: the global Künneth map
  is compatible with pullback.
* `Stacks.WeilDeRham.kunnethGlobalMapCanonical_precomp_left`,
  `Stacks.WeilDeRham.kunnethGlobalMapCanonical_precomp_right`: the global Künneth map for a left
  or right projection that factors.
* `Stacks.WeilDeRham.pullbackSections_naturality`: `p^*` is natural in the complex.
* `Stacks.WeilDeRham.isIso_pullbackSections_of_isIso`: `p^*` is invertible when `p` is an
  isomorphism.

## Implementation notes

The identification `L(𝟙 X)^* ≅ 𝟭` is
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso`, the left adjoint
companion of `R(𝟙 X)_* ≅ 𝟭`; it is the identification for which the unit laws of the composition
isomorphism of derived pullback hold.

## References

* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.KunnethCupWithClass
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

/-! ### Categorical bookkeeping -/

/-- Transposing `L₂` of the counit of `L₁ ⊣ R₁` under `L₂ ⊣ R₂` and then under `L₁ ⊣ R₁` gives
`R₁` of the unit of `L₂ ⊣ R₂`. -/
private theorem homEquiv_homEquiv_map_counit {C D E : Type*} [Category C] [Category D]
    [Category E] {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₂ : L₂ ⊣ R₂) (K : D) :
    adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (L₂.map (adj₁.counit.app K))) =
      R₁.map (adj₂.unit.app K) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h := adj₂.unit.naturality (adj₁.counit.app K)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h
  rw [← h, Functor.map_comp, Adjunction.right_triangle_components_assoc]

/-- For `F ⊣ G` and `e : G ≅ 𝟭`, the unit followed by `e` and by the induced isomorphism
`F ≅ 𝟭` is the identity. -/
private theorem unit_comp_hom_comp_leftAdjointIdIso_hom {C : Type*} [Category C]
    {F G : C ⥤ C} (adj : F ⊣ G) (e : G ≅ 𝟭 C) (K : C) :
    adj.unit.app K ≫ e.hom.app (F.obj K) ≫ (adj.leftAdjointIdIso e).hom.app K = 𝟙 K := by
  have h₁ := e.hom.naturality (F.map (e.inv.app K))
  have h₂ := adj.unit.naturality (e.inv.app K)
  have h₃ := e.hom.naturality (adj.counit.app K)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h₁ h₂ h₃
  rw [Adjunction.leftAdjointIdIso_hom_app, ← reassoc_of% h₁, ← reassoc_of% h₂]
  simp only [← h₃, Adjunction.right_triangle_components_assoc, Iso.inv_hom_id_app]
  rfl

/-- Cancelling `F.map i.inv` against `F.map i.hom` at the end of a composite. -/
private theorem comp_comp_map_hom_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B₁ B₂ B₃ B₄ : D} {P Q : C} (x₁ : A ⟶ B₁) (x₂ : B₁ ⟶ B₂) (x₃ : B₂ ⟶ B₃)
    (x₄ : B₃ ⟶ F.obj P) (z₁ : A ⟶ B₄) (z₂ : B₄ ⟶ F.obj Q) (i : P ≅ Q)
    (h : x₁ ≫ x₂ ≫ x₃ ≫ x₄ = z₁ ≫ z₂ ≫ F.map i.inv) :
    x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ F.map i.hom = z₁ ≫ z₂ := by
  simp only [← Category.assoc] at h ⊢
  rw [h, Category.assoc, ← Functor.map_comp]
  simp

/-- Replacing a composite through a naturality square. -/
private theorem comp_eq_of_comp_eq_of_naturality {C : Type*} [Category C]
    {A B D E F G H : C} {x₀ : A ⟶ B} {m₁ : B ⟶ D} {m₂ : D ⟶ E} {e : E ⟶ F} {s : F ⟶ G}
    {m₃ : B ⟶ H} {e' : H ⟶ G} {n : E ⟶ H} (hn : n ≫ e' = e ≫ s) (hc : m₁ ≫ m₂ ≫ n = m₃) :
    x₀ ≫ m₁ ≫ m₂ ≫ e ≫ s = x₀ ≫ m₃ ≫ e' := by
  rw [← hn, ← hc]
  simp only [Category.assoc]

/-- A composite of images under `F`, with an inserted factor `t ≫ t' = 𝟙`, whose preimage
composite is the identity. -/
private theorem map_comp_comp_map_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q R : C} {B : D} {u : P ⟶ Q} {v : Q ⟶ R} {w : R ⟶ P} (t : F.obj R ⟶ B)
    (t' : B ⟶ F.obj R) (ht : t ≫ t' = 𝟙 _) (hk : u ≫ v ≫ w = 𝟙 P) :
    (F.map u ≫ (F.map v ≫ t) ≫ t') ≫ F.map w = 𝟙 (F.obj P) := by
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  simpa using congrArg F.map hk

/-- An identity obtained through a naturality square. -/
private theorem comp_eq_id_of_naturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A E : D} {P R : C} {x : A ⟶ F.obj P} {m : P ⟶ R} {e : F.obj R ⟶ E} {s : E ⟶ A}
    {n : R ⟶ P} {e' : F.obj P ⟶ A} (hn : F.map n ≫ e' = e ≫ s) (hc : m ≫ n = 𝟙 P)
    (he : x ≫ e' = 𝟙 A) : x ≫ F.map m ≫ e ≫ s = 𝟙 A := by
  rw [← hn, ← Category.assoc (F.map m), ← Functor.map_comp, hc, F.map_id,
    Category.id_comp, he]

/-- The bookkeeping of `kunnethGlobalMapCanonical_comp_pullbackSections`: a pullback square
for the cup products, a naturality square, and two componentwise identities. -/
private theorem comp_cup_pullback_eq {C D : Type*} [Category C] [Category D] (B : C × C ⥤ C)
    (G : D ⥤ C) {P₁ P₂ Q₁ Q₂ R₁ R₂ Z₁ Z₂ E : C} {N₁ N₂ N₃ : D}
    {x₁ : P₁ ⟶ Q₁} {x₂ : P₂ ⟶ Q₂} {u₁ : Q₁ ⟶ R₁} {u₂ : Q₂ ⟶ R₂} {v₁ : R₁ ⟶ Z₁}
    {v₂ : R₂ ⟶ Z₂} {y₁ : P₁ ⟶ Z₁} {y₂ : P₂ ⟶ Z₂} {cW : B.obj (Q₁, Q₂) ⟶ E}
    {t : E ⟶ G.obj N₁} {s₁ : N₁ ⟶ N₂} {s₂ : N₂ ⟶ N₃} {cW' : B.obj (R₁, R₂) ⟶ G.obj N₂}
    {cW'' : B.obj (Z₁, Z₂) ⟶ G.obj N₃} {k : B.obj (P₁, P₂) ⟶ E}
    {k' : B.obj (P₁, P₂) ⟶ G.obj N₃}
    (hk : B.map (x₁ ×ₘ x₂) ≫ cW = k) (hk' : B.map (y₁ ×ₘ y₂) ≫ cW'' = k')
    (hcup : B.map (u₁ ×ₘ u₂) ≫ cW' = cW ≫ t ≫ G.map s₁)
    (hnat : B.map (v₁ ×ₘ v₂) ≫ cW'' = cW' ≫ G.map s₂)
    (h₁ : x₁ ≫ u₁ ≫ v₁ = y₁) (h₂ : x₂ ≫ u₂ ≫ v₂ = y₂) :
    k ≫ t ≫ G.map (s₁ ≫ s₂) = k' := by
  subst hk hk' h₁ h₂
  rw [G.map_comp, Category.assoc, ← reassoc_of% hcup, ← hnat, ← B.map_comp_assoc,
    ← B.map_comp_assoc]
  simp only [prod_comp, Category.assoc]

/-- The bookkeeping of `kunnethGlobalMapCanonical_precomp_left`: naturality of the cup product
in the first variable and a componentwise identity. -/
private theorem eq_tensor_comp_comp_map {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D) (G : D ⥤ C) {P₁ P₂ Q₁ : C} {N₁ N₁' N₂ : D}
    {z : P₁ ⟶ Q₁} {x : Q₁ ⟶ G.obj N₁} {w : N₁ ⟶ N₁'} {y : P₁ ⟶ G.obj N₁'}
    {r : P₂ ⟶ G.obj N₂}
    {c : (T.obj (G.obj N₁)).obj (G.obj N₂) ⟶ G.obj ((T'.obj N₁).obj N₂)}
    {c'' : (T.obj (G.obj N₁')).obj (G.obj N₂) ⟶ G.obj ((T'.obj N₁').obj N₂)}
    {k : (T.obj P₁).obj P₂ ⟶ G.obj ((T'.obj N₁').obj N₂)}
    {k₂ : (T.obj Q₁).obj P₂ ⟶ G.obj ((T'.obj N₁).obj N₂)}
    (hk : (Functor.uncurry.obj T).map (y ×ₘ r) ≫ c'' = k)
    (hk₂ : (Functor.uncurry.obj T).map (x ×ₘ r) ≫ c = k₂)
    (hnat : (Functor.uncurry.obj T).map (G.map w ×ₘ G.map (𝟙 N₂)) ≫ c'' =
      c ≫ G.map ((Functor.uncurry.obj T').map (w ×ₘ 𝟙 N₂)))
    (h : z ≫ x ≫ G.map w = y) :
    k = (T.map z).app P₂ ≫ k₂ ≫ G.map ((T'.map w).app N₂) := by
  subst hk hk₂ h
  rw [← Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right,
    ← Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right, Category.assoc, ← hnat,
    G.map_id, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [prod_comp, Category.assoc, Category.id_comp, Category.comp_id]

/-- The bookkeeping of `kunnethGlobalMapCanonical_precomp_right`: naturality of the cup product
in the second variable and a componentwise identity. -/
private theorem eq_tensor_comp_comp_map_right {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D) (G : D ⥤ C) {P₁ P₂ Q₂ : C} {N₁ N₂ N₂' : D}
    {r : P₁ ⟶ G.obj N₁} {z : P₂ ⟶ Q₂} {x : Q₂ ⟶ G.obj N₂} {w : N₂ ⟶ N₂'}
    {y : P₂ ⟶ G.obj N₂'}
    {c : (T.obj (G.obj N₁)).obj (G.obj N₂) ⟶ G.obj ((T'.obj N₁).obj N₂)}
    {c'' : (T.obj (G.obj N₁)).obj (G.obj N₂') ⟶ G.obj ((T'.obj N₁).obj N₂')}
    {k : (T.obj P₁).obj P₂ ⟶ G.obj ((T'.obj N₁).obj N₂')}
    {k₂ : (T.obj P₁).obj Q₂ ⟶ G.obj ((T'.obj N₁).obj N₂)}
    (hk : (Functor.uncurry.obj T).map (r ×ₘ y) ≫ c'' = k)
    (hk₂ : (Functor.uncurry.obj T).map (r ×ₘ x) ≫ c = k₂)
    (hnat : (Functor.uncurry.obj T).map (G.map (𝟙 N₁) ×ₘ G.map w) ≫ c'' =
      c ≫ G.map ((Functor.uncurry.obj T').map (𝟙 N₁ ×ₘ w)))
    (h : z ≫ x ≫ G.map w = y) :
    k = (T.obj P₁).map z ≫ k₂ ≫ G.map ((T'.obj N₁).map w) := by
  subst hk hk₂ h
  rw [← Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left T P₁ z,
    ← Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left T' N₁ w, Category.assoc,
    ← hnat,
    G.map_id, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [prod_comp, Category.assoc, Category.id_comp, Category.comp_id]

/-- Transposition of a natural transformation `A ⋙ L ⟶ B` under `L ⊣ R` is natural. -/
private theorem homEquiv_app_naturality {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : E ⥤ C) (B : E ⥤ D) (τ : A ⋙ L ⟶ B)
    {K K' : E} (φ : K ⟶ K') :
    A.map φ ≫ adj.homEquiv _ _ (τ.app K') = adj.homEquiv _ _ (τ.app K) ≫ R.map (B.map φ) := by
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  exact congrArg _ (τ.naturality φ)

/-- Moving a morphism across three naturality squares. -/
private theorem comp_three_naturality {C : Type*} [Category C] {A A' B B' D D' E E' : C}
    {x : A ⟶ A'} {i : A ⟶ B} {i' : A' ⟶ B'} {y : B ⟶ B'} {l : B ⟶ D} {l' : B' ⟶ D'}
    {z : D ⟶ D'} {j : D ⟶ E} {j' : D' ⟶ E'} {w : E ⟶ E'} (h₁ : x ≫ i' = i ≫ y)
    (h₂ : y ≫ l' = l ≫ z) (h₃ : z ≫ j' = j ≫ w) : x ≫ i' ≫ l' ≫ j' = (i ≫ l ≫ j) ≫ w := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- A morphism `P` with `P ≫ Q ≫ c` invertible, where `c` is invertible and `Q` has a right
factor `r` with `Q ≫ r` invertible, is invertible. -/
private theorem isIso_of_comp_isIso {C : Type*} [Category C] {A B D E F : C} (P : A ⟶ B)
    (Q : B ⟶ D) (c : D ⟶ E) [IsIso c] (r : D ⟶ F) {I : A ⟶ E} {J : B ⟶ F} [IsIso I] [IsIso J]
    (h₁ : P ≫ Q ≫ c = I) (h₂ : Q ≫ r = J) : IsIso P := by
  have : IsSplitMono Q := IsSplitMono.mk' ⟨r ≫ inv J, by rw [reassoc_of% h₂, IsIso.hom_inv_id]⟩
  have : IsSplitEpi (Q ≫ c) :=
    IsSplitEpi.mk' ⟨inv I ≫ P, by rw [Category.assoc, h₁, IsIso.inv_hom_id]⟩
  have : IsIso (Q ≫ c) := isIso_of_mono_of_isSplitEpi _
  exact IsIso.of_isIso_fac_right h₁

variable {S X Y W W' X' Y' : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-! ### The pullback leg -/

/-- **The pullback leg is the pushed-forward unit.**  For `p ≫ a`, the adjoint
`Ra_*K ⟶ R(p ≫ a)_*Lp^*K` of the counit leg is `Ra_*` of the unit of `Lp^* ⊣ Rp_*` followed by
the composition isomorphism `Ra_* Rp_* ≅ R(p ≫ a)_*` of derived pushforward. -/
theorem pullbackLeg_comp_eq (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pullbackLeg a p (p ≫ a) rfl K =
      (derivedPushforward a).map ((derivedAdjunction p).unit.app K) ≫
        (derivedPushforwardCompIso p a).hom.app ((derivedPullback p).obj K) := by
  unfold pullbackLeg
  rw [← derivedAdjunction_comp_homEquiv]
  congr 1
  rw [pullbackCounitLeg_app_comp]
  simp only [Iso.hom_inv_id_app_assoc]
  exact homEquiv_homEquiv_map_counit (derivedAdjunction a) (derivedAdjunction p) K

/-- The pullback leg for a factorization `p ≫ a = f`: the pushed-forward unit of
`pullbackLeg_comp_eq`, transported along `R(p ≫ a)_* = Rf_*`. -/
theorem pullbackLeg_eq (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pullbackLeg a p f hp K =
      (derivedPushforward a).map ((derivedAdjunction p).unit.app K) ≫
        (derivedPushforwardCompIso p a).hom.app ((derivedPullback p).obj K) ≫
          eqToHom (by rw [hp]) := by
  subst hp
  rw [pullbackLeg_comp_eq, eqToHom_refl, Category.comp_id]

/-- **The pullback legs compose.**  The leg of `p` followed by the leg of `g` and by `R_*` of the
composition isomorphism `Lg^*Lp^* ≅ L(g ≫ p)^*` is the leg of `g ≫ p`. -/
theorem pullbackLeg_comp_comp (g : W' ⟶ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pullbackLeg a p (p ≫ a) rfl K ≫
        pullbackLeg (p ≫ a) g (g ≫ p ≫ a) rfl ((derivedPullback p).obj K) ≫
        (derivedPushforward (g ≫ p ≫ a)).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g p).hom.app K) =
      pullbackLeg a (g ≫ p) ((g ≫ p) ≫ a) rfl K := by
  rw [pullbackLeg_comp_eq, pullbackLeg_comp_eq, pullbackLeg_comp_eq]
  have h := map_unit_comp_derivedPushforwardCompIso_comp a p g K
  simp only [Category.assoc] at h ⊢
  exact comp_comp_map_hom_eq _ _ _ _ _ _ _
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g p).app K) h

/-- **The pullback leg of the identity is the identity**, read through `L(𝟙 X)^* ≅ 𝟭`. -/
theorem pullbackLeg_id (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pullbackLeg a (𝟙 X) a (Category.id_comp a) K ≫ (derivedPushforward a).map
      ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).hom.app K) =
      𝟙 _ := by
  rw [pullbackLeg_eq,
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardCompIso_id_comp]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact map_comp_comp_map_eq_id (derivedPushforward a) _ _
    ((Category.id_comp _).trans (eqToHom_refl _ _))
    (unit_comp_hom_comp_leftAdjointIdIso_hom (derivedAdjunction (𝟙 X))
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso X) K)

/-! ### Functoriality of the pullback map and of the global Künneth map -/

/-- **The pullback map on derived global sections is functorial.**  For `p ≫ a = f` and
`g : W' ⟶ W`, the pullback `RΓ(X, K) ⟶ RΓ(W, Lp^*K)` followed by the pullback
`RΓ(W, Lp^*K) ⟶ RΓ(W', Lg^*Lp^*K)` and the composition isomorphism `Lg^*Lp^* ≅ L(g ≫ p)^*` is
the pullback along `g ≫ p`. -/
theorem pullbackSections_comp (g : W' ⟶ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pullbackSections a p f hp K ≫ pullbackSections f g (g ≫ f) rfl ((derivedPullback p).obj K) ≫
        (sectionsOverBase (g ≫ f)).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g p).hom.app K) =
      pullbackSections a (g ≫ p) (g ≫ f) (by rw [Category.assoc, hp]) K := by
  subst hp
  have hn := (lerayIso (g ≫ p ≫ a)).hom.naturality
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g p).hom.app K)
  have hc := congrArg (baseSections S).map (pullbackLeg_comp_comp a p g K)
  simp only [Functor.map_comp] at hc
  simp only [pullbackSections, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact comp_eq_of_comp_eq_of_naturality hn hc

/-- **The pullback map along the identity is the identity**, read through the identification
`L(𝟙 X)^* ≅ 𝟭` that is the left adjoint companion of `R(𝟙 X)_* ≅ 𝟭`. -/
theorem pullbackSections_id (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pullbackSections a (𝟙 X) a (Category.id_comp a) K ≫ (sectionsOverBase a).map
      ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).hom.app K) =
      𝟙 _ := by
  have hn := (lerayIso a).hom.naturality
    ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).hom.app K)
  simp only [pullbackSections, Category.assoc]
  exact comp_eq_id_of_naturality (baseSections S) hn (pullbackLeg_id a K)
    (Iso.inv_hom_id_app _ _)

/-- **The global Künneth map is compatible with pullback.**  For `g : W' ⟶ W`, the global
Künneth map through `W` followed by the pullback along `g`, the comparison
`Lg^*(Lp^*K ⊗ Lq^*M) ⟶ Lg^*Lp^*K ⊗ Lg^*Lq^*M` and the composition isomorphisms
`Lg^*Lp^* ≅ L(g ≫ p)^*`, `Lg^*Lq^* ≅ L(g ≫ q)^*` is the global Künneth map through `W'` for
the projections `g ≫ p` and `g ≫ q`. -/
theorem kunnethGlobalMapCanonical_comp_pullbackSections (g : W' ⟶ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethGlobalMapCanonical a b p q f hp hq K M ≫
        pullbackSections f g (g ≫ f) rfl
          (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
            ((derivedPullback q).obj M)) ≫
        (sectionsOverBase (g ≫ f)).map
          ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g).app
              ((derivedPullback p).obj K, (derivedPullback q).obj M) ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf)).map
              ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g p).hom.app
                  K ×ₘ
                (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g q).hom.app
                  M)) =
      kunnethGlobalMapCanonical a b (g ≫ p) (g ≫ q) (g ≫ f) (by rw [Category.assoc, hp])
        (by rw [Category.assoc, hq]) K M :=
  comp_cup_pullback_eq (Functor.uncurry.obj (tensorBase S)) (sectionsOverBase (g ≫ f))
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a b p q f hp hq K M)
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a b (g ≫ p) (g ≫ q) (g ≫ f)
      (by rw [Category.assoc, hp]) (by rw [Category.assoc, hq]) K M)
    (cupProductPullbackCompatible f g (g ≫ f) rfl _ _)
    (cupProductOverBase_naturality _ _ _)
    (pullbackSections_comp a p f hp g K) (pullbackSections_comp b q f hq g M)

/-- **The global Künneth map for a left projection that factors.**  If the left projection is
`p' ≫ h` for `h : X' ⟶ X`, the global Künneth map is the pullback along `h` in the first
factor, followed by the global Künneth map over `X'` for `p'` and by the composition isomorphism
`Lp'^*Lh^* ≅ L(p' ≫ h)^*` in the first tensor factor. -/
theorem kunnethGlobalMapCanonical_precomp_left (h : X' ⟶ X) (p' : W ⟶ X')
    (hp' : p' ≫ (h ≫ a) = f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethGlobalMapCanonical a b (p' ≫ h) q f (by rw [Category.assoc, hp']) hq K M =
      ((tensorBase S).map (pullbackSections a h (h ≫ a) rfl K)).app
          ((sectionsOverBase b).obj M) ≫
        kunnethGlobalMapCanonical (h ≫ a) b p' q f hp' hq ((derivedPullback h).obj K) M ≫
        (sectionsOverBase f).map
          (((derivedTensorProductFunctor W.sheaf).map
            ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p' h).hom.app
              K)).app ((derivedPullback q).obj M)) := by
  subst hp'
  exact eq_tensor_comp_comp_map (tensorBase S) (derivedTensorProductFunctor W.sheaf)
    (sectionsOverBase (p' ≫ h ≫ a))
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a b (p' ≫ h) q (p' ≫ h ≫ a)
      (by rw [Category.assoc]) hq K M)
    (kunnethOverBase_eq_kunnethGlobalMapCanonical (h ≫ a) b p' q (p' ≫ h ≫ a) rfl hq
      ((derivedPullback h).obj K) M)
    (cupProductOverBase_naturality _ _ _)
    (pullbackSections_comp a h (h ≫ a) rfl p' K)

/-- **The global Künneth map for a right projection that factors.**  If the right projection is
`q' ≫ h` for `h : Y' ⟶ Y`, the global Künneth map is the pullback along `h` in the second
factor, followed by the global Künneth map over `Y'` for `q'` and by the composition isomorphism
`Lq'^*Lh^* ≅ L(q' ≫ h)^*` in the second tensor factor. -/
theorem kunnethGlobalMapCanonical_precomp_right (h : Y' ⟶ Y) (q' : W ⟶ Y')
    (hq' : q' ≫ (h ≫ b) = f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethGlobalMapCanonical a b p (q' ≫ h) f hp (by rw [Category.assoc, hq']) K M =
      ((tensorBase S).obj ((sectionsOverBase a).obj K)).map
          (pullbackSections b h (h ≫ b) rfl M) ≫
        kunnethGlobalMapCanonical a (h ≫ b) p q' f hp hq' K ((derivedPullback h).obj M) ≫
        (sectionsOverBase f).map
          (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).map
            ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical q' h).hom.app
              M)) := by
  subst hq'
  exact eq_tensor_comp_comp_map_right (tensorBase S) (derivedTensorProductFunctor W.sheaf)
    (sectionsOverBase (q' ≫ h ≫ b))
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a b p (q' ≫ h) (q' ≫ h ≫ b) hp
      (by rw [Category.assoc]) K M)
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a (h ≫ b) p q' (q' ≫ h ≫ b) hp rfl K
      ((derivedPullback h).obj M))
    (cupProductOverBase_naturality _ _ _)
    (pullbackSections_comp b h (h ≫ b) rfl q' M)

/-- **The pullback map on derived global sections is natural** in the complex. -/
theorem pullbackSections_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ K') :
    (sectionsOverBase a).map φ ≫ pullbackSections a p f hp K' =
      pullbackSections a p f hp K ≫ (sectionsOverBase f).map ((derivedPullback p).map φ) := by
  have h₂ := congrArg (baseSections S).map (homEquiv_app_naturality (derivedAdjunction f)
    (derivedPushforward a) (derivedPullback p)
    (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p f hp) φ)
  simp only [Functor.map_comp] at h₂
  unfold pullbackSections pullbackLeg
  exact comp_three_naturality ((lerayIso a).inv.naturality φ) h₂
    ((lerayIso f).hom.naturality ((derivedPullback p).map φ))

/-- The pullback map along an endomorphism equal to the identity, over a base map equal to `a`,
is invertible. -/
theorem isIso_pullbackSections_of_eq_id (q : X ⟶ X) (f' : X ⟶ S) (hq : q ≫ a = f')
    (hq₁ : q = 𝟙 X) (hf : f' = a)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (pullbackSections a q f' hq K) := by
  subst hq₁ f'
  exact IsIso.of_isIso_fac_right (pullbackSections_id a K)

/-- **The pullback map along an isomorphism is an isomorphism.**  If `p` is an isomorphism of
ringed spaces, `p^* : RΓ(X, K) ⟶ RΓ(W, Lp^*K)` is an isomorphism in `D(A)`: by functoriality,
`p^*` followed by `(p⁻¹)^*` and by `p^*` again are the pullbacks along `p⁻¹ ≫ p = 𝟙` and
`p ≫ p⁻¹ = 𝟙`, which are invertible. -/
theorem isIso_pullbackSections_of_isIso [IsIso p]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (pullbackSections a p f hp K) := by
  have := isIso_pullbackSections_of_eq_id a (inv p ≫ p) (inv p ≫ f)
    (by rw [Category.assoc, hp]) (IsIso.inv_hom_id p)
    (by rw [← hp, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]) K
  have := isIso_pullbackSections_of_eq_id f (p ≫ inv p) (p ≫ inv p ≫ f)
    (by rw [Category.assoc]) (IsIso.hom_inv_id p)
    (by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]) ((derivedPullback p).obj K)
  exact isIso_of_comp_isIso _ _ _ _ (pullbackSections_comp a p f hp (inv p) K)
    (pullbackSections_comp f (inv p) (inv p ≫ f) rfl p ((derivedPullback p).obj K))

end Stacks.WeilDeRham
