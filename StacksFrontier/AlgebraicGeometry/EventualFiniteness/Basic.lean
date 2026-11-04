module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Eventual finiteness in an inverse limit of schemes

Let `S` be a quasi-compact and quasi-separated scheme and let `X = lim Xᵢ` be a directed inverse
limit of quasi-compact and quasi-separated schemes over `S` whose transition morphisms are finite
and whose structure morphisms are locally of finite type.  If `X → S` is integral, then `Xᵢ → S`
is finite for all sufficiently large `i`.

The proof follows the Stacks project.  Since finiteness is stable under composition and the
structure morphism at a later index factors through the transition morphism, it suffices to find a
*single* index `k` with `X_k → S` finite, and because finiteness is Zariski-local on the target it
suffices to work over each member of a finite affine open cover `S = V₁ ∪ ⋯ ∪ Vₙ`.  Over a fixed
affine `V`, the preimage of `V` in the limit is affine, so
`AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` (Stacks 01Z6, applied to the diagram of
preimages of an open supplied by `AlgebraicGeometry.opensDiagram`) makes the preimage of `V`
affine at some stage `j₀`.  Writing `R = Γ(S, V)`, `A = Γ(X_{j₀}, p_{j₀}⁻¹V)` and
`A' = Γ(X, f⁻¹V)`, the ring map `R → A` is of finite type, so `A` is generated over `R` by a
finite set `s`; each generator becomes integral over `R` in `A'`, and
`AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit` moves each witnessing monic relation to a
finite stage.  Since the index category is thin, a single further stage `j` dominates all of them,
and there the whole image of `A` is integral over `R`; as `A_j` is module-finite over `A` it is
then integral over `R` as well.  Finally an integral morphism which is locally of finite type is
finite, by `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.RingTheory.EventualFiniteness.isIntegral_comp_of_isIntegralElem_image`: if `φ : A → B` is
  integral and the image of `A` in `B` is integral over `R`, then `B` is integral over `R`.
* `AlgebraicGeometry.EventualFiniteness.exists_isAffineOpen_and_isIntegral_app_of_isLimit`: over a
  fixed affine open of the base, the preimage is eventually affine and the ring map eventually
  integral.
* `AlgebraicGeometry.Scheme.exists_isFinite_app_of_isLimit`: some member of a cofiltered inverse
  system of qcqs schemes with finite transition morphisms, locally of finite type over a qcqs
  base, is finite over the base as soon as the limit is integral over the base.
* `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral`: the directed-preorder form of
  the previous statement, phrased with `Filter.atTop`.

## Implementation notes

The index category is only assumed cofiltered and thin (`CategoryTheory.Quiver.IsThin`); thinness
is what lets a cofinal object be found by `CategoryTheory.IsCofiltered.inf_objs_exists` without
also having to arrange commuting triangles, and it holds for the opposite of a preorder.

In the main results the scheme universe and the index universe are taken to be *equal*.  This is
forced by `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, every declaration of which is stated
for `I : Type u` with `[Category.{u} I]` and `D : I ⥤ Scheme.{u}`; freeing the index universe would
require a cofinal reindexing of the diagram by a category small relative to the scheme universe,
which is an extra hypothesis on the index category rather than a consequence of the data.  The two
naturality lemmas `AlgebraicGeometry.EventualFiniteness.map_comp_app` and
`AlgebraicGeometry.EventualFiniteness.app_map_eq_zero_of_comp` do not touch that machinery, so they
are stated with the index universe and the index-category hom level free.

Several of the auxiliary lemmas below are `.hom`-level restatements of Mathlib lemmas about
morphisms of `CommRingCat`.  They are needed because rewriting with the categorical statement
leaves the implicit type arguments of `CommRingCat.Hom.hom` referring to the un-composed open,
after which no further rewrite applies.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace Stacks.RingTheory.EventualFiniteness

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]

/-- Let `ψ : R → A` and `φ : A → B` be ring maps with `φ` integral.  If every element of the image
of `φ` is integral over `R`, then `B` is integral over `R`.  This is [Stacks, Tag 00GL] in the form
needed for [Stacks, Tag 09ZN]. -/
theorem isIntegral_comp_of_isIntegralElem_image (ψ : R →+* A) (φ : A →+* B) (hφ : φ.IsIntegral)
    (hint : ∀ a : A, (φ.comp ψ).IsIntegralElem (φ a)) :
    (φ.comp ψ).IsIntegral := by
  let _ : Algebra R B := (φ.comp ψ).toAlgebra
  set A' := Algebra.adjoin R (Set.range φ)
  have hmem : ∀ a : A, φ a ∈ A' := fun a ↦ Algebra.subset_adjoin ⟨a, rfl⟩
  have : Algebra.IsIntegral R A' :=
    Algebra.IsIntegral.adjoin (by rintro x ⟨a, rfl⟩; exact hint a)
  have : Algebra.IsIntegral A' B := by
    refine ⟨fun b ↦ ?_⟩
    obtain ⟨p, hp, hpb⟩ := hφ b
    refine ⟨p.map (φ.codRestrict A' hmem), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, show (algebraMap A' B).comp (φ.codRestrict A' hmem) = φ from
      RingHom.ext fun _ ↦ rfl]
    exact hpb
  exact fun b ↦ (Algebra.IsIntegral.trans (R := R) A' (B := B)).isIntegral b

/-- If a generating set of `A` as an `R`-algebra has integral image in `B`, then the whole image of
`A` in `B` is integral over `R`.  The generating condition is phrased with `Subring.closure` so
that the statement does not mention an `Algebra` instance. -/
theorem isIntegralElem_image_of_gens (ψ : R →+* A) (φ : A →+* B) (s : Set A)
    (hgen : ∀ a : A, a ∈ Subring.closure (Set.range ψ ∪ s))
    (hint : ∀ x ∈ s, (φ.comp ψ).IsIntegralElem (φ x)) :
    ∀ a : A, (φ.comp ψ).IsIntegralElem (φ a) := by
  let _ : Algebra R B := (φ.comp ψ).toAlgebra
  have key : Subring.closure (Set.range ψ ∪ s) ≤ (integralClosure R B).toSubring.comap φ := by
    rw [Subring.closure_le]
    rintro x (⟨r, rfl⟩ | hx)
    · exact isIntegral_algebraMap
    · exact hint x hx
  exact fun a ↦ key (hgen a)

/-- A ring map of finite type admits a finite set of algebra generators, in the form used by
`Stacks.RingTheory.EventualFiniteness.isIntegralElem_image_of_gens`. -/
theorem exists_finset_gens (ψ : R →+* A) (hψ : ψ.FiniteType) :
    ∃ s : Finset A, ∀ a : A, a ∈ Subring.closure (Set.range ψ ∪ (s : Set A)) := by
  let _ : Algebra R A := ψ.toAlgebra
  obtain ⟨s, hs⟩ := hψ.1
  refine ⟨s, fun a ↦ ?_⟩
  have h : (Algebra.adjoin R (s : Set A)).toSubring = Subring.closure
      (Set.range (algebraMap R A) ∪ (s : Set A)) := Algebra.adjoin_eq_ring_closure _
  rw [hs, RingHom.algebraMap_toAlgebra] at h
  rw [← h]
  trivial

end Stacks.RingTheory.EventualFiniteness

namespace AlgebraicGeometry

/-- The underlying-ring-map form of `AlgebraicGeometry.Scheme.Hom.comp_app`. -/
lemma Scheme.Hom.comp_app_hom {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (U : Z.Opens) :
    ((a ≫ b).app U).hom = (a.app (b ⁻¹ᵁ U)).hom.comp ((b.app U).hom) := by
  conv_lhs => rw [Scheme.Hom.comp_app]
  exact CommRingCat.hom_comp _ _

/-- The underlying-ring-map form of `AlgebraicGeometry.morphismRestrict_app`. -/
lemma morphismRestrict_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (W : U.toScheme.Opens) :
    ((f ∣_ U).app W).hom =
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op).hom.comp
        ((f.app (U.ι ''ᵁ W)).hom) := by
  conv_lhs => rw [morphismRestrict_app]
  exact CommRingCat.hom_comp _ _

/-- If the ring map of `f` over an open `U` is integral, so is the ring map of `f ∣_ U` over
`⊤`. -/
lemma isIntegral_app_top_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (h : RingHom.IsIntegral ((f.app U).hom)) :
    RingHom.IsIntegral (((f ∣_ U).app ⊤).hom) := by
  rw [morphismRestrict_app_hom f U ⊤]
  refine (RingHom.isIntegral_respectsIso.cancel_right_isIso (f.app (U.ι ''ᵁ ⊤))
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).mpr ?_
  rwa [Scheme.Opens.ι_image_top]

/-- The affine-target criterion for integrality: a morphism to an affine scheme with affine source
whose ring map is integral is integral. -/
@[ega "II 6.1.2" "special case"]
lemma isIntegralHom_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (hX : IsAffine X) (hf : RingHom.IsIntegral (f.app ⊤).hom) : IsIntegralHom f :=
  (@HasAffineProperty.iff_of_isAffine _ _ IsIntegralHom.hasAffineProperty _ _ f _).mpr ⟨hX, hf⟩

/-- Integrality of morphisms of schemes is Zariski-local on the target. -/
lemma isIntegralHom_of_iSup_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*}
    (U : ι → Y.Opens) (hU : iSup U = ⊤) (h : ∀ k, IsIntegralHom (f ∣_ U k)) :
    IsIntegralHom f :=
  @IsZariskiLocalAtTarget.of_iSup_eq_top _
    (@HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty)
    _ _ f _ U hU h

/-- If the composite `a ≫ b` is a morphism of schemes and a section is killed by `b` over an open
`U`, then it is killed by `a ≫ b` over `U`. -/
lemma app_eq_zero_of_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) (hs : (b.app U).hom s = 0) : ((a ≫ b).app U).hom s = 0 := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply,
    hs, map_zero]

namespace EventualFiniteness

section FreeIndexUniverse

/-! The two naturality lemmas below have proofs that constrain neither the index universe nor the
index-category hom level, so they are stated with both free.  The declarations after this section
keep the merged-universe binders, which is what
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` requires. -/

variable {I : Type w} [Category.{v} I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S)

/-- Naturality of a transformation to a constant diagram: the structure morphism at `j` is the
transition morphism followed by the structure morphism at `k`. -/
lemma map_comp_app {j k : I} (g : j ⟶ k) : D.map g ≫ t.app k = t.app j := by
  simp [t.naturality g]

/-- The preimage of `V` under the structure morphism at `j`, pulled back along a transition
morphism `g : k ⟶ j`, is the preimage of `V` under the structure morphism at `k`. -/
private lemma preimage_map_preimage_eq {j k : I} (g : k ⟶ j) (V : S.Opens) :
    D.map g ⁻¹ᵁ (t.app j ⁻¹ᵁ V) = t.app k ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, map_comp_app]

/-- A section killed by one transition morphism is killed by any transition morphism factoring
through it. -/
lemma app_map_eq_zero_of_comp {j k l : I} (g : k ⟶ l) (h : j ⟶ k) (U : (D.obj l).Opens)
    (s : Γ(D.obj l, U)) (hs : ((D.map g).app U).hom s = 0) :
    ((D.map (h ≫ g)).app U).hom s = 0 := by
  rw [D.map_comp h g]
  exact app_eq_zero_of_comp _ _ _ _ hs

end FreeIndexUniverse

variable {I : Type u} [Category.{u} I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D)

variable [IsCofiltered I] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [∀ i, CompactSpace (D.obj i)] in
include c in
/-- Let `{ Dᵢ }` be a cofiltered inverse system of qcqs schemes with affine transition morphisms
and let `U` be a quasi-compact open of `Dᵢ`. If the preimage of `U` in the limit is affine, then
the preimage of `U` at some later stage is affine. -/
lemma exists_isAffineOpen_map_preimage_of_isLimit (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i : I} (U : (D.obj i).Opens) (hU : IsCompact (U : Set (D.obj i)))
    (h : IsAffineOpen (c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (g : j ⟶ i), IsAffineOpen (D.map g ⁻¹ᵁ U) := by
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i U).pt := h
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i U)
  exact ⟨j.left, j.hom, hj⟩

open Stacks.RingTheory.EventualFiniteness in
include c in
/-- The affine-base case of [Stacks, Tag 09ZN].  Over a fixed affine open `V` of the base, the
preimage of `V` is affine and the ring map `Γ(S, V) → Γ(Dⱼ, pⱼ⁻¹V)` is integral at some stage `j`
below any prescribed index. -/
lemma exists_isAffineOpen_and_isIntegral_app_of_isLimit
    [Quiver.IsThin I] [QuasiSeparatedSpace S] (hc : IsLimit c) (f : c.pt ⟶ S) [IsIntegralHom f]
    (hf : ∀ i, f = c.π.app i ≫ t.app i)
    [∀ {i j : I} (g : i ⟶ j), IsFinite (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)]
    (i : I) (V : S.Opens) (hV : IsAffineOpen V) :
    ∃ (j : I) (_ : j ⟶ i), IsAffineOpen (t.app j ⁻¹ᵁ V) ∧
      RingHom.IsIntegral (((t.app j).app V).hom) := by
  classical
  have : ∀ j : I, QuasiSeparatedSpace ↥(((Functor.const I).obj S).obj j) :=
    fun _ ↦ inferInstanceAs (QuasiSeparatedSpace ↥S)
  have hUcpt : IsCompact ((t.app i ⁻¹ᵁ V : (D.obj i).Opens) : Set (D.obj i)) :=
    QuasiCompact.isCompact_preimage (f := t.app i) _ V.2 hV.isCompact
  have hlim : IsAffineOpen (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage, ← hf i]; exact hV.preimage f
  obtain ⟨j₀, g₀, haff₀⟩ :=
    exists_isAffineOpen_map_preimage_of_isLimit D c hc (t.app i ⁻¹ᵁ V) hUcpt hlim
  have haff : IsAffineOpen (t.app j₀ ⁻¹ᵁ V) := by
    rwa [← preimage_map_preimage_eq D t g₀]
  obtain rfl := hf j₀
  have hintlim : RingHom.IsIntegral ((((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
      (((t.app j₀).app V).hom)) := by
    rw [← Scheme.Hom.comp_app_hom]
    exact IsIntegralHom.isIntegral_app _ V hV
  have hftype : RingHom.FiniteType (((t.app j₀).app V).hom) := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (t.app j₀) inferInstance ⟨V, hV⟩
      ⟨t.app j₀ ⁻¹ᵁ V, haff⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at h
  obtain ⟨s, hs⟩ := exists_finset_gens _ hftype
  have key : ∀ x : Γ(D.obj j₀, t.app j₀ ⁻¹ᵁ V), ∃ (j : I) (g : j ⟶ j₀)
      (P : Polynomial Γ(S, V)), P.Monic ∧
      (((D.map g).app (t.app j₀ ⁻¹ᵁ V)).hom)
        (Polynomial.eval₂ (((t.app j₀).app V).hom) x P) = 0 := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hintlim (((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom x)
    have h0 : (((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom)
        (Polynomial.eval₂ (((t.app j₀).app V).hom) x P) = 0 := by
      rw [Polynomial.hom_eval₂]; exact hPx
    obtain ⟨j, g, hg⟩ := exists_app_map_eq_zero_of_isLimit D c hc
      (U := t.app j₀ ⁻¹ᵁ V) haff.isCompact _ h0
    exact ⟨j, g, P, hP, hg⟩
  choose jx gx Px hPxmonic hPxzero using key
  obtain ⟨k, T⟩ := IsCofiltered.inf_objs_exists (insert j₀ (s.image jx))
  obtain ⟨g₁⟩ := T (Finset.mem_insert_self _ _)
  have hintim : ∀ a : Γ(D.obj j₀, t.app j₀ ⁻¹ᵁ V),
      ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
        (((t.app j₀).app V).hom)).IsIntegralElem
          ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) a) := by
    refine isIntegralElem_image_of_gens (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) _ hs ?_
    intro x hx
    refine ⟨Px x, hPxmonic x, ?_⟩
    refine (Polynomial.hom_eval₂ (Px x) (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) x).symm.trans ?_
    have hmem : jx x ∈ insert j₀ (s.image jx) :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
    rw [show g₁ = (T hmem).some ≫ gx x from Subsingleton.elim _ _]
    exact app_map_eq_zero_of_comp D (gx x) _ _ _ (hPxzero x)
  have hintring : RingHom.IsIntegral (((D.map g₁ ≫ t.app j₀).app V).hom) := by
    rw [Scheme.Hom.comp_app_hom]
    exact isIntegral_comp_of_isIntegralElem_image _ _
      (IsFinite.finite_app (D.map g₁) (t.app j₀ ⁻¹ᵁ V) haff).to_isIntegral hintim
  refine ⟨k, g₁ ≫ g₀, ?_, ?_⟩
  · rw [← preimage_map_preimage_eq D t g₁]
    exact haff.preimage (D.map g₁)
  · rw [← map_comp_app D t g₁]
    exact hintring

end EventualFiniteness

open EventualFiniteness in
/-- **Stacks 09ZN**, cofiltered form.  Let `{ Dᵢ }` be a cofiltered inverse system of qcqs schemes
over a qcqs base `S`, with finite transition morphisms and structure morphisms locally of finite
type.  If the induced morphism from the limit to `S` is integral, then some `Dᵢ → S` is finite. -/
lemma Scheme.exists_isFinite_app_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    [Quiver.IsThin I] {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S) [IsIntegralHom f] (hf : ∀ i, f = c.π.app i ≫ t.app i)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsFinite (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)] :
    ∃ k : I, IsFinite (t.app k) := by
  classical
  obtain ⟨i₁⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun U : S.affineOpens ↦ ((U : S.Opens) : Set S)) (fun U ↦ (U : S.Opens).2) (by
      intro x _
      have h : x ∈ (⨆ U : S.affineOpens, (U : S.Opens)) := by
        rw [iSup_affineOpens_eq_top S]; trivial
      simpa using h)
  have key : ∀ U : S.affineOpens, ∃ (j : I) (_ : j ⟶ i₁),
      IsAffineOpen (t.app j ⁻¹ᵁ (U : S.Opens)) ∧
        RingHom.IsIntegral (((t.app j).app (U : S.Opens)).hom) :=
    fun U ↦ exists_isAffineOpen_and_isIntegral_app_of_isLimit D t c hc f hf i₁ U U.2
  choose jU _ hjU using key
  obtain ⟨k, T⟩ := IsCofiltered.inf_objs_exists (σ.image jU)
  refine ⟨k, (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨?_, inferInstance⟩⟩
  refine isIntegralHom_of_iSup_eq_top _ (fun U : {U // U ∈ σ} ↦ ((U.1 : S.Opens))) ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_iSup]
    refine Set.eq_univ_of_univ_subset (hσ.trans ?_)
    simp only [Set.iUnion_subset_iff]
    intro U hU
    exact Set.subset_iUnion_of_subset ⟨U, hU⟩ le_rfl
  · intro U
    obtain ⟨h⟩ := T (Finset.mem_image_of_mem _ U.2)
    show IsIntegralHom (t.app k ∣_ ((U.1 : S.Opens)))
    have : IsAffine ((U.1 : S.Opens)).toScheme := U.1.2
    have hA : IsAffineOpen (t.app k ⁻¹ᵁ ((U.1 : S.Opens))) := by
      rw [← preimage_map_preimage_eq D t h]
      exact (hjU U.1).1.preimage (D.map h)
    have hI : RingHom.IsIntegral (((t.app k).app ((U.1 : S.Opens))).hom) := by
      rw [← map_comp_app D t h, Scheme.Hom.comp_app_hom]
      exact RingHom.isIntegral_stableUnderComposition _ _ (hjU U.1).2
        (IsFinite.finite_app (D.map h) _ (hjU U.1).1).to_isIntegral
    exact isIntegralHom_of_isAffine _ hA (isIntegral_app_top_morphismRestrict _ _ hI)

open EventualFiniteness in
/-- **Stacks 09ZN** for a directed preorder.  In a directed inverse system of qcqs schemes over a
qcqs scheme, if the transition morphisms are finite, the stages are locally of finite type over the
base, and the limit is integral over the base, then the stages are eventually finite over the base.

The index type is taken in the same universe as the schemes; see the module docstring. -/
@[stacks 09ZN]
theorem eventually_isFinite_of_isLimit_of_isIntegral
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (p : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ i, f = c.π.app (Opposite.op i) ≫ p.app (Opposite.op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (Opposite.op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (Opposite.op i))]
    (haffine : ∀ {i j : I} (h : i ≤ j),
      IsAffineHom (F.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j),
      IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (p.app (Opposite.op i))] :
    ∀ᶠ i in Filter.atTop, IsFinite (p.app (Opposite.op i)) := by
  have : ∀ k : Iᵒᵖ, CompactSpace (F.obj k) :=
    fun k ↦ inferInstanceAs (CompactSpace ↥(F.obj (Opposite.op k.unop)))
  have : ∀ k : Iᵒᵖ, QuasiSeparatedSpace (F.obj k) :=
    fun k ↦ inferInstanceAs (QuasiSeparatedSpace ↥(F.obj (Opposite.op k.unop)))
  have : ∀ k : Iᵒᵖ, LocallyOfFiniteType (p.app k) :=
    fun k ↦ inferInstanceAs (LocallyOfFiniteType (p.app (Opposite.op k.unop)))
  have : ∀ {k l : Iᵒᵖ} (g : k ⟶ l), IsAffineHom (F.map g) := by
    intro k l g
    exact haffine (leOfHom g.unop)
  have : ∀ {k l : Iᵒᵖ} (g : k ⟶ l), IsFinite (F.map g) := by
    intro k l g
    exact hfinite (leOfHom g.unop)
  obtain ⟨k, hk⟩ := Scheme.exists_isFinite_app_of_isLimit F p c hc f (fun k ↦ hf k.unop)
  rw [Filter.eventually_atTop]
  refine ⟨k.unop, fun j hj ↦ ?_⟩
  have := hk
  rw [← map_comp_app F p (homOfLE hj).op]
  infer_instance

end AlgebraicGeometry
