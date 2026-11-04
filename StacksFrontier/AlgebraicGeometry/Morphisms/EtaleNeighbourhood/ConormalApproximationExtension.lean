module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximation

/-!
# Stacks 0CAY with the comparison hypothesis taken over the finite type extension

The scheme-level statement `exists_finiteType_pointed_extension_conormalAlgebra_iso` carries the
comparison of conormal algebras as the hypothesis
`Stacks.ConormalApproximation.HasUniformConormalBound`, which asks for a single `N` making
*any* two maps `𝒪_{T,t} → 𝒪_{S,s}^∧` congruent modulo `𝔪_s^N` give isomorphic conormal algebras.
That property is false: see
`Stacks.ConormalApproximation.not_exists_uniform_congruence_bound`, where
`Y = Spec(D[a][x]/(a x))` over `T = Spec(D[a])` over `S = Spec(D)` and the maps `a ↦ 0` and
`a ↦ u^N` agree modulo `(u)^N` while the degree `N` parts of the two conormal algebras are not
even isomorphic as modules over the associated graded ring.

The source does not claim it either. In Stacks 0CAY the congruence that is used is a congruence
of the *syzygy coefficients*, that is, a congruence of two maps out of the finite type extension
`C' = C[t_{kj,I}]/(…)` of Stacks 0CB0, not of two maps out of `𝒪_{T,t}`. This file carries the
comparison in that shape, as
`Stacks.ConormalApproximation.HasConormalBoundAlongExtension`, and deduces Stacks 0CAY from it
by one further application of Stacks 0CAX, now over the extension — which is exactly step seven
of the source's proof.

## Main definitions

* `Stacks.ConormalApproximation.pointedStalkMap`: the map on stalks induced by a morphism of
  pointed schemes, the composite spelt out in Stacks 0CAX.
* `Stacks.ConormalApproximation.HasConormalBoundAlongExtension`: a pointed finite type extension
  `(T₁, t₁) → (T, t)` through which `σ` factors, together with a bound `N` on congruences of maps
  out of `𝒪_{T₁,t₁}` forcing `HasConormalIso`.

## Main results

* `Stacks.ConormalApproximation.pointedStalkMap_comp`: the induced maps compose.
* `Stacks.ConormalApproximation.eq_of_spec_fromSpecStalk_eq` and
  `Stacks.ConormalApproximation.eq_comp_pointedStalkMap_of_spec_eq`: a local homomorphism out of a
  stalk is determined by the morphism from the spectrum of the local ring it induces, and two such
  homomorphisms inducing the same morphism are composites of one another along the morphism of
  pointed schemes. `Stacks.ConormalApproximation.spec_comp_of_pointedStalkMap` is the converse
  computation and `Stacks.ConormalApproximation.closedPoint_specMap_fromSpecStalk` locates the
  closed point.
* `Stacks.ConormalApproximation.exists_pointed_extension_fibreProduct`: **two pointed finite type
  extensions through which `σ` factors are dominated by one**, namely their fibre product over
  `T`. This is the merging step of the source's first paragraph, by which the finitely many
  conditions coming from a cover of `Y` by affine opens are reduced to a single extension, and
  `Stacks.ConormalApproximation.exists_pointed_extension_merge_family` is its iterate over a
  finite family, the `T'_1 ×_T ⋯ ×_T T'_n` the source writes.
* `Stacks.ConormalApproximation.pointedStalkMap_id`: the identity induces the identity.
* `Stacks.ConormalApproximation.exists_finiteType_pointed_extension_conormalAlgebra_iso_of_bound`:
  Stacks 0CAY, relative to `HasConormalBoundAlongExtension`. The hypothesis is discharged
  downstream, and the unconditional statement carrying `@[stacks 0CAY]` is
  `exists_finiteType_pointed_extension_conormalAlgebra_iso_of_isLocalHom`.

## Implementation notes

Relative to `exists_finiteType_pointed_extension_conormalAlgebra_iso` two things change. The
comparison hypothesis is taken over the extension, which is what makes it a consequence of the
affine statement `exists_finiteType_coefficients_associatedGraded_equiv` rather than a false
statement. And the geometric input of the source's first step is no longer a hypothesis: the two
closed immersions `Y_t ↪ Y_σ` and `Y_t ↪ Y_{σ'}` are supplied by
`hasFibreImmersion_of_isLocalHom`, which applies because `σ` is local — it factors as
`τ ∘ 𝒪_{T,t} → 𝒪_{T₁,t₁}` with `τ` local — and `σ'` is local by hypothesis.

### The factorisation of `σ'` carries no condition

The source says only that `σ'` "factors through `𝒪_{T,t} → 𝒪_{T',t'}`", putting no condition on
the factorising map `τ' : 𝒪_{T',t'} → 𝒪_{S,s}^∧`, and the antecedent here is that existential and
nothing more: `∃ τ', σ' = τ' ∘ (𝒪_{T,t} → 𝒪_{T',t'})`. Locality is asserted of `σ'` itself, which
is what the source assumes ("every local `𝒪_{S,s}`-algebra map `σ'`"), and of the factorisation
`τ` of `σ` that the extension is produced with, which is a conclusion rather than a hypothesis.

What made the weaker antecedent `∃ τ', IsLocalHom τ' ∧ …` look unavoidable is the inner
application of Stacks 0CAX over `T₁` below: its `σ'` is `τ' ∘ (𝒪_{T,t} → 𝒪_{T₁,t₁})`, and
locality of that composite does not follow from locality of `σ'` — writing `𝔭 = (τ')⁻¹(𝔪)`, a
non-local `τ'` factors through the localisation `𝒪_{T₁,z}` at the point `z` of `T₁` that `𝔭`
names, and locality of `σ'` forces only `g z = t` and `t₁ ∈ closure {z}`, so the proper
generalisations of `t₁` in the fibre `g⁻¹(t)` are genuinely admitted. Nor can the congruence be
taken over `𝒪_{T,t}` instead, where it is false by
`Stacks.ConormalApproximation.not_exists_uniform_congruence_bound`.

The way out is the one the source takes: the congruence of 0CAX is established on an affine
chart ring, not on a local ring, and there no locality is available or needed. That is
`AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow_of_factors`,
0CAX with the locality of `σ'` dropped from its agreement clause — the relations cut out of
`Γ(T, V)[t_{kj,I}]` force the congruence on `Γ(T, V)` for *every* algebra map out of the
extension ring, and `agreement_mod_ideal_of_localization` carries it to the stalk because both
maps are already defined on the localisation. Applied to `τ' ∘ (𝒪_{T,t} → 𝒪_{T₁,t₁})` it needs
nothing of `τ'`, and `Stacks.ConormalApproximation.HasConormalBoundAlongExtension` needs nothing
of it either, so the source's antecedent is what the statement below carries.

Noetherianness of the extension is carried as part of the existential. It is a consequence of
`LocallyOfFiniteType` over a Noetherian base (Stacks 01T6) and may be dropped once that is
available.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
* [Stacks Project, Tag 0CAX](https://stacks.math.columbia.edu/tag/0CAX)
* [Stacks Project, Tag 0CB0](https://stacks.math.columbia.edu/tag/0CB0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.ConormalApproximation

/-- The map on stalks induced by a morphism of pointed schemes `(X, x) → (Y, y)`. -/
noncomputable def pointedStalkMap {X Y : Scheme.{u}} (g : X ⟶ Y) {x : X} {y : Y} (h : g x = y) :
    Y.presheaf.stalk y →+* X.presheaf.stalk x :=
  (g.stalkMap x).hom.comp (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) h).symm).hom

/-- The maps on stalks induced by composable morphisms of pointed schemes compose. -/
theorem pointedStalkMap_comp {X Y Z : Scheme.{u}} (g₂ : X ⟶ Y) (g : Y ⟶ Z)
    {x : X} {y : Y} {z : Z} (h₂ : g₂ x = y) (h : g y = z) (h' : (g₂ ≫ g) x = z) :
    (pointedStalkMap g₂ h₂).comp (pointedStalkMap g h) = pointedStalkMap (g₂ ≫ g) h' := by
  simp only [pointedStalkMap]
  simp only [Scheme.Hom.comp_apply] at h' ⊢
  cases h₂
  cases h
  have he : h' = (rfl : g (g₂ x) = g (g₂ x)) := Subsingleton.elim _ _
  have hcast : (eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h').symm).hom =
      RingHom.id _ := by
    rw [he]
    rfl
  rw [hcast, RingHom.comp_id]
  simp only [eqToHom_refl, CommRingCat.hom_id, RingHom.comp_id]
  ext a
  simp only [Scheme.Hom.stalkMap_comp, RingHom.comp_apply]
  rfl

/-- The identity of a pointed scheme induces the identity on the stalk. -/
theorem pointedStalkMap_id {X : Scheme.{u}} (x : X) (h : (𝟙 X : X ⟶ X) x = x) :
    pointedStalkMap (𝟙 X) h = RingHom.id (X.presheaf.stalk x) := by
  have hz : pointedStalkMap (𝟙 X) h =
      ((𝟙 X : X ⟶ X).stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) h).symm).hom := rfl
  rw [hz, Scheme.Hom.stalkMap_id, Subsingleton.elim h (rfl : (𝟙 X : X ⟶ X) x = x)]
  rfl

/-- The map on stalks induced by a morphism of pointed schemes is a local homomorphism. -/
instance isLocalHom_pointedStalkMap {X Y : Scheme.{u}} (g : X ⟶ Y) {x : X} {y : Y}
    (h : g x = y) : IsLocalHom (pointedStalkMap g h) := by
  subst h
  simp only [pointedStalkMap, eqToHom_refl, CommRingCat.hom_id, RingHom.comp_id]
  infer_instance

/-! ### Merging two pointed finite type extensions through which `σ` factors

The first step of Stacks 0CAY merges finitely many conditions on the factorisation of `σ` by
replacing the extensions they ask for with their fibre product `T'_1 ×_T ⋯ ×_T T'_n` over `T`.
This section performs the binary case, which is the whole content: the two maps
`Spec(𝒪_{S,s}^∧) → T'_i` that `τ_i` determines agree over `T`, so they lift to the fibre product,
and the closed point of `Spec(𝒪_{S,s}^∧)` is the point of the fibre product above `t`. -/

section Merge

/-- A local homomorphism out of a stalk is determined by the morphism from the spectrum of the
local ring that it induces: the uniqueness half of
`AlgebraicGeometry.SpecToEquivOfLocalRing`, at a fixed point. -/
theorem eq_of_spec_fromSpecStalk_eq {Y : Scheme.{u}} {D : Type u} [CommRing D] [IsLocalRing D]
    {y : Y} (α β : Y.presheaf.stalk y ⟶ CommRingCat.of D)
    [IsLocalHom α.hom] [IsLocalHom β.hom]
    (h : Spec.map α ≫ Y.fromSpecStalk y = Spec.map β ≫ Y.fromSpecStalk y) : α = β := by
  have hsig : (⟨y, α, inferInstance⟩ :
      Σ z : Y, { f : Y.presheaf.stalk z ⟶ CommRingCat.of D // IsLocalHom f.hom }) =
      ⟨y, β, inferInstance⟩ :=
    (SpecToEquivOfLocalRing (X := Y) (R := CommRingCat.of D)).symm.injective h
  exact Subtype.ext_iff.mp (eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp hsig).2)

/-- Composing a homomorphism out of the stalk at `x` with the map on stalks of a morphism of
pointed schemes is, on spectra, composing with that morphism. -/
theorem spec_comp_of_pointedStalkMap {X Y : Scheme.{u}} {D : Type u} [CommRing D]
    (g : X ⟶ Y) {x : X} {y : Y} (h : g x = y) (phi : X.presheaf.stalk x →+* D) :
    Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x ≫ g =
      Spec.map (CommRingCat.ofHom (phi.comp (pointedStalkMap g h))) ≫ Y.fromSpecStalk y := by
  subst h
  simp only [pointedStalkMap, eqToHom_refl, CommRingCat.hom_id, RingHom.comp_id]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk g, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The morphism `Spec(D) ⟶ X` determined by a local homomorphism out of the stalk at `x` carries
the closed point of `Spec(D)` to `x`. -/
theorem closedPoint_specMap_fromSpecStalk {X : Scheme.{u}} (x : X) {D : Type u} [CommRing D]
    [IsLocalRing D] (phi : X.presheaf.stalk x →+* D) [IsLocalHom phi] :
    (Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x)
      (closedPoint ↥(CommRingCat.of D)) = x :=
  (congrArg (X.fromSpecStalk x).base (Spec_closedPoint (f := CommRingCat.ofHom phi))).trans
    Scheme.fromSpecStalk_closedPoint

/-- Conversely, two local homomorphisms out of the stalks at `x` and at `y = g x` inducing the
same morphism from the spectrum of a local ring are composites of one another along `g`. -/
theorem eq_comp_pointedStalkMap_of_spec_eq {X Y : Scheme.{u}} {D : Type u} [CommRing D]
    [IsLocalRing D] (g : X ⟶ Y) {x : X} {y : Y} (h : g x = y)
    (phi : X.presheaf.stalk x →+* D) [IsLocalHom phi]
    (psi : Y.presheaf.stalk y →+* D) [IsLocalHom psi]
    (hcomm : Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x ≫ g =
      Spec.map (CommRingCat.ofHom psi) ≫ Y.fromSpecStalk y) :
    psi = phi.comp (pointedStalkMap g h) := by
  subst h
  simp only [pointedStalkMap, eqToHom_refl, CommRingCat.hom_id, RingHom.comp_id]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk g, ← Category.assoc, ← Spec.map_comp] at hcomm
  have : IsLocalHom (g.stalkMap x ≫ CommRingCat.ofHom phi).hom := by
    show IsLocalHom (phi.comp (g.stalkMap x).hom)
    infer_instance
  exact congrArg CommRingCat.Hom.hom
    (eq_of_spec_fromSpecStalk_eq (Y := Y) (D := D) (y := g x)
      (CommRingCat.ofHom psi) (g.stalkMap x ≫ CommRingCat.ofHom phi) hcomm.symm)

open CategoryTheory.Limits in
/-- **Two pointed finite type extensions through which `σ` factors are dominated by one.**
The fibre product `T₁ ×_T T₂` carries a point above `t`, through which `σ` factors by a local
homomorphism restricting to the two given factorisations. This is the merging step of Stacks
0CAY, by which finitely many conditions on the extension are reduced to one.

Noetherianness of the fibre product is not asserted: it needs finite type over a Noetherian
base to imply Noetherian (Stacks 01T6), which is not available here, exactly as for the
extension carried in `HasConormalBoundAlongExtension`. -/
theorem exists_pointed_extension_fibreProduct
    {S T T₁ T₂ : Scheme.{u}} [IsNoetherian S] (s : S) (t : T)
    (sigma : T.presheaf.stalk t →+* completedStalk S s)
    (g₁ : T₁ ⟶ T) (t₁ : T₁) (hg₁ : g₁ t₁ = t)
    (g₂ : T₂ ⟶ T) (t₂ : T₂) (hg₂ : g₂ t₂ = t)
    [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    [LocallyOfFiniteType g₂] [QuasiCompact g₂]
    (tau₁ : T₁.presheaf.stalk t₁ →+* completedStalk S s) (htau₁ : IsLocalHom tau₁)
    (hfact₁ : sigma = tau₁.comp (pointedStalkMap g₁ hg₁))
    (tau₂ : T₂.presheaf.stalk t₂ →+* completedStalk S s) (htau₂ : IsLocalHom tau₂)
    (hfact₂ : sigma = tau₂.comp (pointedStalkMap g₂ hg₂)) :
    ∃ (T₃ : Scheme.{u}) (q₁ : T₃ ⟶ T₁) (q₂ : T₃ ⟶ T₂) (t₃ : T₃)
      (h₁ : q₁ t₃ = t₁) (h₂ : q₂ t₃ = t₂),
      LocallyOfFiniteType q₁ ∧ QuasiCompact q₁ ∧
      LocallyOfFiniteType q₂ ∧ QuasiCompact q₂ ∧
      q₁ ≫ g₁ = q₂ ≫ g₂ ∧
      ∃ tau₃ : T₃.presheaf.stalk t₃ →+* completedStalk S s,
        IsLocalHom tau₃ ∧
        tau₁ = tau₃.comp (pointedStalkMap q₁ h₁) ∧
        tau₂ = tau₃.comp (pointedStalkMap q₂ h₂) := by
  have := htau₁
  have := htau₂
  let w₁ : Spec (CommRingCat.of (completedStalk S s)) ⟶ T₁ :=
    Spec.map (CommRingCat.ofHom tau₁) ≫ T₁.fromSpecStalk t₁
  let w₂ : Spec (CommRingCat.of (completedStalk S s)) ⟶ T₂ :=
    Spec.map (CommRingCat.ofHom tau₂) ≫ T₂.fromSpecStalk t₂
  have e₁ := spec_comp_of_pointedStalkMap g₁ hg₁ tau₁
  have e₂ := spec_comp_of_pointedStalkMap g₂ hg₂ tau₂
  rw [← hfact₁] at e₁
  rw [← hfact₂] at e₂
  have hcomm : w₁ ≫ g₁ = w₂ ≫ g₂ := by
    show (Spec.map (CommRingCat.ofHom tau₁) ≫ T₁.fromSpecStalk t₁) ≫ g₁ =
      (Spec.map (CommRingCat.ofHom tau₂) ≫ T₂.fromSpecStalk t₂) ≫ g₂
    rw [Category.assoc, Category.assoc, e₁, e₂]
  let q₁ : pullback g₁ g₂ ⟶ T₁ := pullback.fst g₁ g₂
  let q₂ : pullback g₁ g₂ ⟶ T₂ := pullback.snd g₁ g₂
  let w : Spec (CommRingCat.of (completedStalk S s)) ⟶ pullback g₁ g₂ :=
    pullback.lift w₁ w₂ hcomm
  have hw₁ : w ≫ q₁ = w₁ := pullback.lift_fst _ _ _
  have hw₂ : w ≫ q₂ = w₂ := pullback.lift_snd _ _ _
  have h₁ : q₁ (w (closedPoint ↥(CommRingCat.of (completedStalk S s)))) = t₁ :=
    (congrArg (fun m : Spec (CommRingCat.of (completedStalk S s)) ⟶ T₁ =>
        m.base (closedPoint ↥(CommRingCat.of (completedStalk S s)))) hw₁).trans
      (closedPoint_specMap_fromSpecStalk t₁ tau₁)
  have h₂ : q₂ (w (closedPoint ↥(CommRingCat.of (completedStalk S s)))) = t₂ :=
    (congrArg (fun m : Spec (CommRingCat.of (completedStalk S s)) ⟶ T₂ =>
        m.base (closedPoint ↥(CommRingCat.of (completedStalk S s)))) hw₂).trans
      (closedPoint_specMap_fromSpecStalk t₂ tau₂)
  refine ⟨pullback g₁ g₂, q₁, q₂, w (closedPoint ↥(CommRingCat.of (completedStalk S s))),
    h₁, h₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ g₂).flip inferInstance
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ g₂).flip inferInstance
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ g₂) inferInstance
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ g₂) inferInstance
  · exact pullback.condition
  · have hspec : Spec.map (Scheme.stalkClosedPointTo w) ≫
        (pullback g₁ g₂).fromSpecStalk
          (w (closedPoint ↥(CommRingCat.of (completedStalk S s)))) = w :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk w
    refine ⟨(Scheme.stalkClosedPointTo w).hom, inferInstance, ?_, ?_⟩
    · refine eq_comp_pointedStalkMap_of_spec_eq q₁ h₁
        ((Scheme.stalkClosedPointTo w).hom) tau₁ ?_
      rw [← Category.assoc]
      exact (congrArg (fun m : Spec (CommRingCat.of (completedStalk S s)) ⟶ pullback g₁ g₂ =>
        m ≫ q₁) hspec).trans hw₁
    · refine eq_comp_pointedStalkMap_of_spec_eq q₂ h₂
        ((Scheme.stalkClosedPointTo w).hom) tau₂ ?_
      rw [← Category.assoc]
      exact (congrArg (fun m : Spec (CommRingCat.of (completedStalk S s)) ⟶ pullback g₁ g₂ =>
        m ≫ q₂) hspec).trans hw₂

/-- **Finitely many pointed finite type extensions through which `σ` factors are dominated by
one.** The iterated fibre product `T'_1 ×_T ⋯ ×_T T'_n` of the source's first paragraph, obtained
from `exists_pointed_extension_fibreProduct` by induction on the number of extensions: there is
one pointed finite type extension `(T', t') → (T, t)` through which `σ` factors by a local
homomorphism `τ`, mapping over `T` to every one of the given extensions compatibly with their
factorisations of `σ`.

The empty case is the identity of `T`, which is where `IsLocalHom σ` is used; for a nonempty
family it is a consequence of the factorisations. -/
theorem exists_pointed_extension_merge_family
    {S T : Scheme.{u}} [IsNoetherian S] (s : S) (t : T)
    (sigma : T.presheaf.stalk t →+* completedStalk S s) (hsigma : IsLocalHom sigma)
    {n : ℕ} (Tf : Fin n → Scheme.{u}) (gf : ∀ k, Tf k ⟶ T) (tf : ∀ k, Tf k)
    (hgf : ∀ k, gf k (tf k) = t)
    (hft : ∀ k, LocallyOfFiniteType (gf k)) (hqc : ∀ k, QuasiCompact (gf k))
    (tauf : ∀ k, (Tf k).presheaf.stalk (tf k) →+* completedStalk S s)
    (htauf : ∀ k, IsLocalHom (tauf k))
    (hfactf : ∀ k, sigma = (tauf k).comp (pointedStalkMap (gf k) (hgf k))) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g)
      (tau : T'.presheaf.stalk t' →+* completedStalk S s),
      IsLocalHom tau ∧ sigma = tau.comp (pointedStalkMap g hgt) ∧
      ∀ k, ∃ (q : T' ⟶ Tf k) (hq : q t' = tf k),
        q ≫ gf k = g ∧ tauf k = tau.comp (pointedStalkMap q hq) := by
  induction n with
  | zero =>
      refine ⟨T, 𝟙 T, t, rfl, inferInstance, inferInstance, sigma, hsigma, ?_, ?_⟩
      · rw [pointedStalkMap_id t rfl]
        exact (RingHom.comp_id sigma).symm
      · exact fun k => k.elim0
  | succ n ih =>
      obtain ⟨T', g, t', hgt, hfin, hqcg, tau, htau, hfact, hmaps⟩ :=
        ih (fun k => Tf k.castSucc) (fun k => gf k.castSucc) (fun k => tf k.castSucc)
          (fun k => hgf k.castSucc) (fun k => hft k.castSucc) (fun k => hqc k.castSucc)
          (fun k => tauf k.castSucc) (fun k => htauf k.castSucc) (fun k => hfactf k.castSucc)
      have := hfin
      have := hqcg
      have := hft (Fin.last n)
      have := hqc (Fin.last n)
      obtain ⟨T₃, q₁, q₂, t₃, h₁, h₂, hfin₁, hqc₁, hfin₂, hqc₂, hcond, tau₃, htau₃, e₁, e₂⟩ :=
        exists_pointed_extension_fibreProduct s t sigma g t' hgt
          (gf (Fin.last n)) (tf (Fin.last n)) (hgf (Fin.last n))
          tau htau hfact (tauf (Fin.last n)) (htauf (Fin.last n)) (hfactf (Fin.last n))
      have := hfin₁
      have := hqc₁
      have hgt₃ : (q₁ ≫ g) t₃ = t := by
        show g (q₁ t₃) = t
        rw [h₁, hgt]
      refine ⟨T₃, q₁ ≫ g, t₃, hgt₃, inferInstance, inferInstance, tau₃, htau₃, ?_, ?_⟩
      · rw [← pointedStalkMap_comp q₁ g h₁ hgt hgt₃, ← RingHom.comp_assoc, ← e₁, hfact]
      · refine Fin.lastCases ?_ ?_
        · refine ⟨q₂, h₂, hcond.symm, e₂⟩
        · intro j
          obtain ⟨q, hq, hqg, hqtau⟩ := hmaps j
          have hq₃ : (q₁ ≫ q) t₃ = tf j.castSucc := by
            show q (q₁ t₃) = tf j.castSucc
            rw [h₁, hq]
          refine ⟨q₁ ≫ q, hq₃, ?_, ?_⟩
          · rw [Category.assoc, hqg]
          · rw [← pointedStalkMap_comp q₁ q h₁ hq hq₃, ← RingHom.comp_assoc, ← e₁, hqtau]

end Merge

/-- **The graded comparison of Stacks 0CAY, in the shape the source proves it.**
There are a pointed finite type extension `(T₁, t₁) → (T, t)` through which `σ` factors, and a
bound `N ≥ 1`, such that any `τ'` out of `𝒪_{T₁,t₁}` congruent to the factorisation `τ` of `σ`
modulo `𝔪_s^N` gives `Y_t ↪ Y_σ` and `Y_t ↪ Y_{σ'}` isomorphic conormal algebras, where
`σ' = τ' ∘ 𝒪_{T,t} → 𝒪_{T₁,t₁}`.

Taking the congruence over `𝒪_{T,t}` instead, as
`Stacks.ConormalApproximation.HasUniformConormalBound` does, gives a property no `N` has: see
`Stacks.ConormalApproximation.not_exists_uniform_congruence_bound`. -/
def HasConormalBoundAlongExtension {S T Y : Scheme.{u}} (p : Y ⟶ T) (s : S) (t : T)
    (sigma : T.presheaf.stalk t →+* completedStalk S s) : Prop :=
  ∃ (T₁ : Scheme.{u}) (g : T₁ ⟶ T) (t₁ : T₁) (hgt : g t₁ = t) (_ : IsNoetherian T₁)
    (_ : LocallyOfFiniteType g) (_ : QuasiCompact g)
    (tau : T₁.presheaf.stalk t₁ →+* completedStalk S s),
    IsLocalHom tau ∧
    sigma = tau.comp (pointedStalkMap g hgt) ∧
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ tau' : T₁.presheaf.stalk t₁ →+* completedStalk S s,
        (∀ a, tau a - tau' a ∈
          Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
            (maximalIdeal (S.presheaf.stalk s) ^ N)) →
        HasConormalIso p t (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t)
          (Spec.map (CommRingCat.ofHom (tau'.comp (pointedStalkMap g hgt))) ≫
            T.fromSpecStalk t)

/-- **Stacks 0CAY**, relative to the comparison hypothesis in the shape the source proves it.
Let `Y → T → S` be finite type morphisms of Noetherian schemes, let `t ∈ T` lie over `s ∈ S` and
let `σ : 𝒪_{T,t} → 𝒪_{S,s}^∧` be a local `𝒪_{S,s}`-algebra map. There is a finite type morphism
of pointed schemes `(T', t') → (T, t)` through which `σ` factors such that for every local
`𝒪_{S,s}`-algebra map `σ' : 𝒪_{T,t} → 𝒪_{S,s}^∧` factoring through `𝒪_{T',t'}` the closed
immersions `Y_σ ← Y_t → Y_{σ'}` have isomorphic conormal algebras.

The hypothesis is `Stacks.ConormalApproximation.HasConormalBoundAlongExtension`, which holds for
every local `σ` by `Stacks.ConormalApproximation.hasConormalBoundAlongExtension_of_isLocalHom`; the
resulting unconditional statement is
`exists_finiteType_pointed_extension_conormalAlgebra_iso_of_isLocalHom`. -/
theorem exists_finiteType_pointed_extension_conormalAlgebra_iso_of_bound
    {S T Y : Scheme.{u}} (f : T ⟶ S) (p : Y ⟶ T)
    [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (s : S) (t : T) (ht : f t = s)
    (sigma : T.presheaf.stalk t →+* completedStalk S s)
    (hsigma_base : sigma.comp (pointedStalkMap f ht) =
      algebraMap (S.presheaf.stalk s) (completedStalk S s))
    (hcompare : HasConormalBoundAlongExtension p s t sigma) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g),
      ∃ tau : T'.presheaf.stalk t' →+* completedStalk S s,
        IsLocalHom tau ∧
        sigma = tau.comp (pointedStalkMap g hgt) ∧
        ∀ sigma' : T.presheaf.stalk t →+* completedStalk S s,
          IsLocalHom sigma' →
          sigma'.comp (pointedStalkMap f ht) =
            algebraMap (S.presheaf.stalk s) (completedStalk S s) →
          (∃ tau' : T'.presheaf.stalk t' →+* completedStalk S s,
            sigma' = tau'.comp (pointedStalkMap g hgt)) →
          HasIsoConormalFibreImmersions p t
            (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t)
            (Spec.map (CommRingCat.ofHom sigma') ≫ T.fromSpecStalk t) := by
  obtain ⟨T₁, g, t₁, hgt, hnoeth, hfin, hqc, tau, htau, hfact, N, hN, hbound⟩ := hcompare
  have hsigma : IsLocalHom sigma := by
    rw [hfact]
    have := htau
    infer_instance
  have := hnoeth
  have := hfin
  have := hqc
  have hgft : (g ≫ f) t₁ = s := by
    show f (g t₁) = s
    rw [hgt, ht]
  have htau_base : tau.comp (pointedStalkMap (g ≫ f) hgft) =
      algebraMap (S.presheaf.stalk s) (completedStalk S s) := by
    rw [← pointedStalkMap_comp g f hgt ht hgft, ← RingHom.comp_assoc, ← hfact]
    exact hsigma_base
  obtain ⟨T₂, g₂, t₂, hg₂, hfin₂, hqc₂, tau₂, htau₂, hfact₂, -, hagree⟩ :=
    AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow_of_factors
      (g ≫ f) s t₁ hgft tau htau htau_base N hN
  have := hfin₂
  have := hqc₂
  have hgt₂ : (g₂ ≫ g) t₂ = t := by
    show g (g₂ t₂) = t
    rw [hg₂, hgt]
  have hfact₂' : tau = tau₂.comp (pointedStalkMap g₂ hg₂) := hfact₂
  refine ⟨T₂, g₂ ≫ g, t₂, hgt₂, inferInstance, inferInstance, tau₂, htau₂, ?_, ?_⟩
  · rw [← pointedStalkMap_comp g₂ g hg₂ hgt hgt₂, ← RingHom.comp_assoc, ← hfact₂', hfact]
  · rintro sigma' hsigma' hsigma'_base ⟨tau₂', hfact'⟩
    have hcomp' : (tau₂'.comp (pointedStalkMap g₂ hg₂)).comp (pointedStalkMap g hgt) = sigma' := by
      rw [RingHom.comp_assoc, pointedStalkMap_comp g₂ g hg₂ hgt hgt₂, ← hfact']
    have hbase' : (tau₂'.comp (pointedStalkMap g₂ hg₂)).comp
        (pointedStalkMap (g ≫ f) hgft) =
        algebraMap (S.presheaf.stalk s) (completedStalk S s) := by
      rw [← pointedStalkMap_comp g f hgt ht hgft, ← RingHom.comp_assoc, hcomp']
      exact hsigma'_base
    have hcong := hagree (tau₂'.comp (pointedStalkMap g₂ hg₂)) hbase'
      ⟨tau₂', rfl⟩
    have hiso := hbound (tau₂'.comp (pointedStalkMap g₂ hg₂)) hcong
    rw [hcomp'] at hiso
    exact ⟨hasFibreImmersion_of_isLocalHom f p s t ht sigma hsigma hsigma_base,
      hasFibreImmersion_of_isLocalHom f p s t ht sigma' hsigma' hsigma'_base, hiso⟩

end Stacks.ConormalApproximation

end
