module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Algebra.Homology.QuasiIsoRoof
import StacksCore.Algebra.Homology.QuasiIso
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedRestriction
import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy

/-!
# Perfect complexes and mapping cones, at the level of complexes

Let `X` be a ringed space. A complex of `𝒪_X`-modules is perfect (Stacks 08CM) when, on the
members of an open covering, it receives quasi-isomorphisms from strictly perfect complexes. This
file proves the basic stability properties of that condition directly on complexes, without any
derived category: perfectness is local, it is invariant under quasi-isomorphisms and under roofs
of quasi-isomorphisms, and the mapping cone of a morphism of perfect complexes is perfect. The
last statement is the content of Stacks 08CR; the statements about objects of a derived category
are deduced from these in `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles`,
for any model of that category.

## Main results

* `CochainComplex.QuasiIsoRoof.restrict`: restriction to an open subspace carries a roof of
  quasi-isomorphisms to one.
* `AlgebraicGeometry.RingedSpace.IsPerfectComplex.exists_local` and
  `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_exists`: perfectness is the existence,
  near every point, of a quasi-isomorphism from a strictly perfect complex.
* `AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_quasiIso`: a roof of
  quasi-isomorphisms `P ⟶ A ⟵ K|_U` with `P` strictly perfect gives, near each point, a
  quasi-isomorphism from a strictly perfect complex to `K`.
* `AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_of_quasiIso` and
  `AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_of_quasiIsoRoof`: perfectness is invariant
  under quasi-isomorphisms and roofs of quasi-isomorphisms.
* `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs`: a complex joined near every
  point to a strictly perfect complex by a roof of quasi-isomorphisms is perfect; this is the
  complex-level form of the local criterion of Stacks 08CN.
* `AlgebraicGeometry.RingedSpace.isPerfectComplex_mappingCone`: the mapping cone of a morphism of
  perfect complexes is perfect (the content of Stacks 08CR).
* `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict`: a complex
  whose restrictions to the members of an open covering are perfect is perfect.

## Implementation notes

Quasi-isomorphisms are passed as explicit hypotheses `QuasiIso f`, not as instances: instance
search for `QuasiIso` does not fit in the default budget inside the large local contexts of these
proofs. They are handled degreewise, through the isomorphisms they induce on cohomology
(`quasiIso_iff_isIso_homologyMap`). The abstract lemmas of the first section are stated for
complexes in an arbitrary abelian category.

The local lifts are those of Stacks 08C8 on an open subspace, read on an open of `X`
(`AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy_of_le`); the proof of Stacks 08CC in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso` uses them in the same way.

All universes of the ringed space coincide, as they must for `StrictlyPerfect.OXMod` to exist.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08C8](https://stacks.math.columbia.edu/tag/08C8)
* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- Composing a quasi-isomorphism with the forward map of an isomorphism gives a
quasi-isomorphism. -/
private theorem quasiIso_comp_iso_hom {A B D : CochainComplex C ℤ} {g : A ⟶ B} (hg : QuasiIso g)
    (e : B ≅ D) : QuasiIso (g ≫ e.hom) :=
  (quasiIso_iff_isIso_homologyMap _).2 fun j => isIso_homologyMap_comp _ _ j
    ((quasiIso_iff_isIso_homologyMap g).1 hg j) (isIso_homologyMap_iso_hom _ j)

/-- A lift up to homotopy of a quasi-isomorphism through a quasi-isomorphism is a
quasi-isomorphism: if `β ≫ φ` is homotopic to `ψ` and `φ`, `ψ` are quasi-isomorphisms, so is
`β`. -/
theorem quasiIso_left_of_homotopy_comp {P A B : CochainComplex C ℤ} {β : P ⟶ B} {φ : B ⟶ A}
    {ψ : P ⟶ A} (H : Homotopy (β ≫ φ) ψ) (hφ : QuasiIso φ) (hψ : QuasiIso ψ) : QuasiIso β :=
  (quasiIso_iff_isIso_homologyMap β).2 fun j => isIso_homologyMap_of_homotopy H j
    ((quasiIso_iff_isIso_homologyMap φ).1 hφ j) ((quasiIso_iff_isIso_homologyMap ψ).1 hψ j)

/-- The morphism of mapping cones induced by a square commuting up to homotopy whose two sides
are quasi-isomorphisms is a quasi-isomorphism: the five lemma on the long exact cohomology
sequences of the two mapping-cone triangles. -/
theorem quasiIso_mapOfHomotopy {P E A B : CochainComplex C ℤ} {γ : P ⟶ E} {f : A ⟶ B}
    {α : P ⟶ A} {β : E ⟶ B} (H : Homotopy (γ ≫ β) (α ≫ f)) (hα : QuasiIso α)
    (hβ : QuasiIso β) : QuasiIso (CochainComplex.mappingCone.mapOfHomotopy H) :=
  (quasiIso_iff_isIso_homologyMap _).2 fun i => by
    have := (quasiIso_iff_isIso_homologyMap α).1 hα i
    have := (quasiIso_iff_isIso_homologyMap β).1 hβ (i + 1)
    exact isIso_homologyMap_mappingCone_of_homotopy H i (IsIso.epi_of_iso _)
      ((quasiIso_iff_isIso_homologyMap β).1 hβ i)
      ((quasiIso_iff_isIso_homologyMap α).1 hα (i + 1)) (IsIso.mono_of_iso _)

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-! ### Restriction and quasi-isomorphisms -/

/-- Restriction to an open subspace preserves quasi-isomorphisms, being exact. -/
theorem quasiIso_restrictComplexMap {A B : CochainComplex (OXMod.{u, u} X) ℤ} (g : A ⟶ B)
    (hg : QuasiIso g) (U : Opens X.carrier) : QuasiIso (restrictComplexMap g U) :=
  (quasiIso_iff_isIso_homologyMap _).2 fun j =>
    isIso_homologyMap_restrictComplexMap g U j ((quasiIso_iff_isIso_homologyMap g).1 hg j)

/-- Restriction to an open subspace carries a roof of quasi-isomorphisms to one, being exact. -/
theorem _root_.CochainComplex.QuasiIsoRoof.restrict {K L : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : CochainComplex.QuasiIsoRoof K L) (U : Opens X.carrier) :
    CochainComplex.QuasiIsoRoof (restrictComplex K U) (restrictComplex L U) := by
  obtain ⟨G, f, s, hf, hs⟩ := CochainComplex.quasiIsoRoof_iff.1 h
  exact CochainComplex.quasiIsoRoof_iff.2 ⟨_, restrictComplexMap f U, restrictComplexMap s U,
    quasiIso_restrictComplexMap f hf U, quasiIso_restrictComplexMap s hs U⟩

/-- Restriction to a smaller open subspace preserves quasi-isomorphisms, being exact. -/
theorem quasiIso_restrictModulesOfLE_map {U V : Opens X.carrier} (h : V ≤ U)
    {A B : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ} (g : A ⟶ B)
    (hg : QuasiIso g) :
    QuasiIso (((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
  (quasiIso_iff_isIso_homologyMap _).2 fun j =>
    isIso_homologyMap_mapHomologicalComplex _ g j ((quasiIso_iff_isIso_homologyMap g).1 hg j)

/-- A quasi-isomorphism from a strictly perfect complex onto the restriction of a complex to `U`
restricts to one onto its restriction to any smaller open `V ≤ U`. -/
theorem exists_restricted_quasiIso {U V : Opens X.carrier} (h : V ≤ U)
    (A : CochainComplex (OXMod.{u, u} X) ℤ)
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P) (α : P ⟶ restrictComplex A U) (hα : QuasiIso α) :
    ∃ Q : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect Q ∧ ∃ β : Q ⟶ restrictComplex A V, QuasiIso β :=
  ⟨((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    isStrictlyPerfect_restrictModulesOfLE h hP,
    ((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫
      (restrictComplexOfLEIso X h A).hom,
    quasiIso_comp_iso_hom (quasiIso_restrictModulesOfLE_map h α hα) _⟩

/-! ### Perfectness is local -/

/-- A perfect complex receives, near every point, a quasi-isomorphism from a strictly perfect
complex: the member of the covering containing the point. -/
theorem IsPerfectComplex.exists_local {E : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : IsPerfectComplex E) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧ ∃ f : P ⟶ restrictComplex E U, QuasiIso f := by
  obtain ⟨I, U, hU, hcov⟩ := h
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ trivial : x ∈ iSup U)
  exact ⟨U i, hi, hcov i⟩

/-- A complex receiving, near every point, a quasi-isomorphism from a strictly perfect complex is
perfect: the neighbourhoods of the points form the covering. -/
theorem isPerfectComplex_of_forall_exists {E : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧ ∃ f : P ⟶ restrictComplex E U, QuasiIso f) :
    IsPerfectComplex E := by
  choose U hx hP using h
  exact ⟨X.carrier, U, top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩, hP⟩

/-- **Straightening a roof.** Let `α : P ⟶ A` and `f : K|_U ⟶ A` be quasi-isomorphisms of
complexes of `𝒪_U`-modules, with `P` strictly perfect. Then every point of `U` has an open
neighbourhood `W ⊆ U` on which `K` receives a quasi-isomorphism from a strictly perfect complex.

Stacks 08C8 lifts `α` through `f` up to homotopy near the point; the lift is a quasi-isomorphism
because `α` and `f` are, and the restriction of `P` stays strictly perfect. -/
theorem exists_local_strictlyPerfect_quasiIso {K : CochainComplex (OXMod.{u, u} X) ℤ}
    {U : Opens X.carrier} {A P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : IsStrictlyPerfect P) (α : P ⟶ A) (hα : QuasiIso α)
    (f : restrictComplex K U ⟶ A) (hf : QuasiIso f) (x : X.carrier) (hxU : x ∈ U) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ P' : CochainComplex (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P' ∧ ∃ β : P' ⟶ restrictComplex K W, QuasiIso β := by
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hP
  obtain ⟨W, hWU, hxW, β, ⟨H⟩⟩ := exists_local_lift_homotopy_of_le α f a hP ha
    (fun j _ => (quasiIso_iff_isIso_homologyMap f).1 hf j)
    (by have := (quasiIso_iff_isIso_homologyMap f).1 hf a; exact IsIso.epi_of_iso _) x hxU
  have hβ := quasiIso_left_of_homotopy_comp H (quasiIso_restrictModulesOfLE_map hWU f hf)
    (quasiIso_restrictModulesOfLE_map hWU α hα)
  exact ⟨W, hxW, _, isStrictlyPerfect_restrictModulesOfLE hWU hP,
    β ≫ (restrictComplexOfLEIso X hWU K).hom,
    quasiIso_comp_iso_hom hβ _⟩

/-! ### Invariance under quasi-isomorphisms -/

/-- Perfectness of a complex passes to the target of a quasi-isomorphism: compose the local
quasi-isomorphisms with its restrictions. -/
theorem IsPerfectComplex.of_quasiIso {E F : CochainComplex (OXMod.{u, u} X) ℤ}
    (hE : IsPerfectComplex E) (s : E ⟶ F) (hs : QuasiIso s) : IsPerfectComplex F := by
  obtain ⟨I, U, hU, hcov⟩ := hE
  refine ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨P, hP, p, hp⟩ := hcov i
  exact ⟨P, hP, p ≫ restrictComplexMap s (U i),
    quasiIso_comp _ _ (hφ := hp) (hφ' := quasiIso_restrictComplexMap s hs (U i))⟩

/-- **Perfectness is invariant under quasi-isomorphisms.** The source of a quasi-isomorphism into
a perfect complex is perfect too: near every point, the quasi-isomorphism from a strictly perfect
complex into the target and the restriction of the given one form a roof, which straightens
(`AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_quasiIso`). -/
theorem isPerfectComplex_iff_of_quasiIso {E F : CochainComplex (OXMod.{u, u} X) ℤ} (s : E ⟶ F)
    (hs : QuasiIso s) : IsPerfectComplex E ↔ IsPerfectComplex F := by
  refine ⟨fun hE => hE.of_quasiIso s hs, fun hF => isPerfectComplex_of_forall_exists fun x => ?_⟩
  obtain ⟨U, hxU, P, hP, p, hp⟩ := hF.exists_local x
  exact exists_local_strictlyPerfect_quasiIso hP p hp (restrictComplexMap s U)
    (quasiIso_restrictComplexMap s hs U) x hxU

/-- **Perfectness is invariant under roofs of quasi-isomorphisms**, hence, in every model of the
derived category, under isomorphisms `Q(E) ≅ Q(F)` (`CochainComplex.quasiIsoRoof_iff_nonempty_iso`).
-/
theorem isPerfectComplex_iff_of_quasiIsoRoof {E F : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : CochainComplex.QuasiIsoRoof E F) : IsPerfectComplex E ↔ IsPerfectComplex F := by
  obtain ⟨G, f, s, hf, hs⟩ := CochainComplex.quasiIsoRoof_iff.1 h
  exact (isPerfectComplex_iff_of_quasiIso f hf).trans (isPerfectComplex_iff_of_quasiIso s hs).symm

/-- **The local criterion for perfectness, at the level of complexes.** A complex which, near
every point, is joined to a strictly perfect complex by a roof of quasi-isomorphisms is perfect.
This is the form of Stacks 08CN in which no derived category occurs: in any model of the derived
category of an open subspace, a roof is the same as an isomorphism
(`CochainComplex.quasiIsoRoof_iff_nonempty_iso`). -/
theorem isPerfectComplex_of_local_roofs {E : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧ CochainComplex.QuasiIsoRoof P (restrictComplex E U)) :
    IsPerfectComplex E := by
  refine isPerfectComplex_of_forall_exists fun x => ?_
  obtain ⟨U, hxU, P, hP, hr⟩ := h x
  obtain ⟨G, α, s, hα, hs⟩ := CochainComplex.quasiIsoRoof_iff.1 hr
  exact exists_local_strictlyPerfect_quasiIso hP α hα s hs x hxU

/-! ### Mapping cones -/

/-- **The mapping cone of a morphism of perfect complexes is perfect** (the content of Stacks
08CR, at the level of complexes).

Near a point, take quasi-isomorphisms `p : 𝒫 ⟶ 𝒜|_U` and `q : 𝒬 ⟶ ℬ|_U` from strictly perfect
complexes over a common open `U`. Stacks 08C8 lifts `p ≫ f|_U` through `q` up to homotopy over a
smaller open `W`, by some `γ : 𝒫|_W ⟶ 𝒬|_W`. The induced morphism of mapping cones
`C(γ) ⟶ C(f)|_W` is a quasi-isomorphism by the five lemma, and `C(γ)` is strictly perfect by
Stacks 08C5. -/
theorem isPerfectComplex_mappingCone {A B : CochainComplex (OXMod.{u, u} X) ℤ} (f : A ⟶ B)
    (hA : IsPerfectComplex A) (hB : IsPerfectComplex B) :
    IsPerfectComplex (CochainComplex.mappingCone f) := by
  refine isPerfectComplex_of_forall_exists fun x => ?_
  obtain ⟨U₁, hx₁, P₁, hP₁, p₁, hp₁⟩ := hA.exists_local x
  obtain ⟨U₂, hx₂, Q₁, hQ₁, q₁, hq₁⟩ := hB.exists_local x
  obtain ⟨P, hP, p, hp⟩ := exists_restricted_quasiIso inf_le_left A P₁ hP₁ p₁ hp₁
  obtain ⟨Q, hQ, q, hq⟩ := exists_restricted_quasiIso inf_le_right B Q₁ hQ₁ q₁ hq₁
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hP
  -- Lift `p ≫ f|_U` through `q` near the point, over an open `W ≤ U := U₁ ⊓ U₂`.
  obtain ⟨W, hWU, hxW, γ, ⟨H⟩⟩ := exists_local_lift_homotopy_of_le
    (p ≫ restrictComplexMap f (U₁ ⊓ U₂)) q a hP ha
    (fun j _ => (quasiIso_iff_isIso_homologyMap q).1 hq j)
    (by have := (quasiIso_iff_isIso_homologyMap q).1 hq a; exact IsIso.epi_of_iso _) x ⟨hx₁, hx₂⟩
  have H' := H.trans (Homotopy.ofEq (Functor.map_comp _ _ _))
  have hcone := quasiIso_mapOfHomotopy H' (quasiIso_restrictModulesOfLE_map hWU p hp)
    (quasiIso_restrictModulesOfLE_map hWU q hq)
  exact ⟨W, hxW, CochainComplex.mappingCone γ,
    isStrictlyPerfect_mappingCone γ (isStrictlyPerfect_restrictModulesOfLE hWU hP)
      (isStrictlyPerfect_restrictModulesOfLE hWU hQ),
    CochainComplex.mappingCone.mapOfHomotopy H' ≫ (mappingConeRestrictComplexOfLEIso X hWU f).hom,
    quasiIso_comp_iso_hom hcone _⟩

/-! ### Perfectness through opens of opens -/

/-- **Perfectness is local on `X`.** A complex of `𝒪_X`-modules whose restrictions to the members
of an open covering are perfect complexes is perfect.

Near a point of `U`, perfectness of the restriction gives a quasi-isomorphism from a strictly
perfect complex on an open `V` of the subspace `U`; the identification of modules on `(X|_U)|_V`
with modules on the image of `V` in `X` carries it over. -/
theorem isPerfectComplex_of_forall_isPerfectComplex_restrict
    {E : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      IsPerfectComplex (X := X.restrict U.isOpenEmbedding) (restrictComplex E U)) :
    IsPerfectComplex E := by
  refine isPerfectComplex_of_forall_exists fun x => ?_
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨V, hxV, P, hP, f, hf⟩ := hU.exists_local ⟨x, hxU⟩
  obtain ⟨g, hg⟩ := exists_quasiIso_nestedComplex U V E f hf
  exact ⟨U.isOpenEmbedding.functor.obj V, ⟨⟨x, hxU⟩, hxV, rfl⟩, nestedComplex U V P,
    isStrictlyPerfect_nestedComplex U V hP, g, hg⟩

end AlgebraicGeometry.RingedSpace

end
