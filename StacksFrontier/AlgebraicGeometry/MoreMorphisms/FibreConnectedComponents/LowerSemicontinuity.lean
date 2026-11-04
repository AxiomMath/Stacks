module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Semicontinuity.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Proper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Lower semicontinuity of the number of geometric connected components of fibres

For an integral, universally open morphism the number of geometric connected components of the
fibres is lower semicontinuous on the target:  the geometric fibres are then totally
disconnected, so the count is a count of points, and `n` distinct points of one geometric fibre
spread out over a neighbourhood because the `n`-fold fibre product of the morphism with itself
is again universally open.  For a flat proper morphism of finite presentation the Stein
factorization transports this to the morphism itself, which is [Stacks, Tag 0BUI].

## Main results

* `AlgebraicGeometry.lowerSemicontinuous_numGeometricConnectedComponents_of_isIntegralHom`:
  lower semicontinuity of the count for an integral, universally open morphism.
* `AlgebraicGeometry.numGeometricConnectedComponents_comp_eq`: a geometrically connected,
  universally closed morphism does not change the count of the morphism it is composed with.
* `AlgebraicGeometry.universallyOpen_of_surjective_comp`: a morphism whose composition with a
  preceding surjection is universally open is itself universally open.
* `AlgebraicGeometry.lowerSemicontinuous_numGeometricConnectedComponents`:
  [Stacks, Tag 0BUI] for a flat proper morphism of finite presentation.

## Implementation notes

The count is the `ℕ∞`-valued `AlgebraicGeometry.numGeometricConnectedComponents` of Tag 055F, so
lower semicontinuity also covers the value `⊤`;  being of finite presentation is expressed, as
usual, by `LocallyOfFinitePresentation` together with the quasi-compactness and
quasi-separatedness that a proper morphism has anyway.

The Stein factorization used is Mathlib's relative normalization `f.normalization`, whose
structure morphism `f.fromNormalization` is integral (Tag 03H2) and which receives
`f.toNormalization` from `X`.  Flatness and local finite presentation make `f` universally open
(Tag 01UA), and `f.toNormalization` is surjective, so `f.fromNormalization` is universally open
as well.

That `f.toNormalization` has geometrically connected fibres is the connectedness conjunct of
clause (1) of [Stacks, Tag 03H2], which Tag 0BUI quotes;  it is
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`.

## References

* [Stacks Project, Tag 0BUI](https://stacks.math.columbia.edu/tag/0BUI)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 055F](https://stacks.math.columbia.edu/tag/055F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A closed morphism with connected fibres induces a bijection on connected components:  it is
a quotient map whose fibres are connected. -/
@[ega "IV 4.4.2" "special case"]
private lemma enatCard_connectedComponents_eq_of_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyConnected f] (hf : IsClosedMap f) :
    ENat.card (_root_.ConnectedComponents X) = ENat.card (_root_.ConnectedComponents Y) := by
  have hq : Topology.IsCoinducing f :=
    (hf.isQuotientMap f.continuous f.surjective).isCoinducing
  exact ENat.card_congr (hq.connectedComponentsHomeomorph f.isConnected_preimage_singleton).toEquiv

/-- Precomposing with a geometrically connected, universally closed morphism does not change the
number of geometric connected components of the fibres:  on the geometric fibre over a point of
the base the first morphism is still closed with connected fibres, so it induces a bijection on
connected components. -/
theorem numGeometricConnectedComponents_comp_eq {X T S : Scheme.{u}} (h : X ⟶ T) (g : T ⟶ S)
    [GeometricallyConnected h] [UniversallyClosed h] :
    numGeometricConnectedComponents (h ≫ g) = numGeometricConnectedComponents g := by
  funext s
  let k := S.residueField s
  let K := SeparableClosure k
  let q₀ := S.fromSpecResidueField s
  let q₁ : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let q : Spec (.of K) ⟶ S := q₁ ≫ q₀
  let eX := pullbackLeftPullbackSndIso (h ≫ g) q₀ q₁
  let eT := pullbackLeftPullbackSndIso g q₀ q₁
  let eH := pullbackRightPullbackFstIso g q h
  let hK := pullback.snd h (pullback.fst g q)
  let directX : Scheme.{u} := pullback (h ≫ g) q
  let nestedX : Scheme.{u} := pullback h (pullback.fst g q)
  let directT : Scheme.{u} := pullback g q
  show ENat.card (_root_.ConnectedComponents (geometricFiber (h ≫ g) s K)) =
    ENat.card (_root_.ConnectedComponents (geometricFiber g s K))
  calc
    ENat.card (_root_.ConnectedComponents (geometricFiber (h ≫ g) s K)) =
        ENat.card (_root_.ConnectedComponents directX) :=
      enatCard_connectedComponents_iso eX
    _ = ENat.card (_root_.ConnectedComponents nestedX) :=
      (enatCard_connectedComponents_iso eH).symm
    _ = ENat.card (_root_.ConnectedComponents directT) :=
      enatCard_connectedComponents_eq_of_geometricallyConnected hK hK.isClosedMap
    _ = ENat.card (_root_.ConnectedComponents (geometricFiber g s K)) :=
      (enatCard_connectedComponents_iso eT).symm

/-- Points of a scheme integral over a field are closed:  the scheme is affine and its ring is
integral over the field, so every prime of it is maximal. -/
private lemma isClosed_singleton_of_isIntegralHom_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsIntegralHom f] (x : X) : IsClosed ({x} : Set X) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  rw [← show X.isoSpec.hom ⁻¹' {p} = {x} by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, p]
    exact X.isoSpec.hom.homeomorph.injective.eq_iff]
  refine ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 ?_).preimage
    X.isoSpec.hom.continuous
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  apply @Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ _ _ _
    f.appTop.hom (isIntegral_appTop_of_universallyClosed f) p.asIdeal p.2
  rw [(Ideal.eq_bot_or_top _).resolve_right (p.2.comap f.appTop.hom).ne_top]
  exact Ideal.bot_isMaximal

/-- A scheme integral over a field is totally disconnected:  it is affine with all points closed,
so its ring has Krull dimension zero and Tag 04MG applies. -/
private lemma totallyDisconnectedSpace_of_isIntegralHom_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsIntegralHom f] : TotallyDisconnectedSpace X := by
  have : T1Space X := ⟨isClosed_singleton_of_isIntegralHom_over_field f⟩
  have : IsAffine X := isAffine_of_isAffineHom f
  let e : X ≃ₜ PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom.homeomorph
  have : T1Space (PrimeSpectrum Γ(X, ⊤)) := e.t1Space
  have : TotallyDisconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    ((spec_profinite_tfae Γ(X, ⊤)).out 6 3).mp (fun p hp =>
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨p, hp⟩).mp isClosed_singleton)
  exact e.symm.totallyDisconnectedSpace

/-- Every point of a scheme integral over an algebraically closed field is the image of a section
of its structure morphism:  the residue field at the point is integral over the field, hence
equal to it. -/
private lemma exists_section_of_isIntegralHom_over_algClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsIntegralHom f] (x : X) :
    ∃ a : Spec (.of K) ⟶ X, a ≫ f = 𝟙 _ ∧ a (IsLocalRing.closedPoint K) = x := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp
      (isClosed_singleton_of_isIntegralHom_over_field f x)
  have : IsIntegralHom (X.fromSpecResidueField x ≫ f) := inferInstance
  let φ := Spec.preimage (X.fromSpecResidueField x ≫ f)
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff]
    simpa only [φ, Spec.map_preimage] using this
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral φ.hom hφ)
  refine ⟨Spec.map (inv φ) ≫ X.fromSpecResidueField x, ?_,
    X.fromSpecResidueField_apply x _⟩
  rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField x ≫ f)]
  show Spec.map (inv φ) ≫ Spec.map φ = _
  rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

/-- Two sections of a morphism to the spectrum of a field agree as soon as they have the same
image point:  the induced maps on residue fields are then both inverse to the same map. -/
private lemma sections_ext_of_apply_eq
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    {a b : Spec (.of K) ⟶ X} (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _)
    (h : a (IsLocalRing.closedPoint K) = b (IsLocalRing.closedPoint K)) : a = b := by
  obtain ⟨⟨x, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨y, β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢
  have hxy : x = y :=
    (X.fromSpecResidueField_apply x _).symm.trans
      (h.trans (X.fromSpecResidueField_apply y _))
  subst y
  let φ := Spec.preimage (X.fromSpecResidueField x ≫ f)
  have hφ (γ : X.residueField x ⟶ .of K) (hγ : Spec.map γ ≫ X.fromSpecResidueField x ≫ f = 𝟙 _) :
      φ ≫ γ = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id, φ, Spec.map_preimage, Category.assoc] using hγ
  have hα := hφ α ha
  have hβ := hφ β hb
  have : IsIso α := (ConcreteCategory.isIso_iff_bijective α).mpr ⟨α.hom.injective, fun k =>
    ⟨φ.hom k, ConcreteCategory.congr_hom hα k⟩⟩
  have : IsIso φ := by
    have : IsIso (φ ≫ α) := hα ▸ inferInstance
    exact IsIso.of_isIso_comp_right φ α
  have hαβ : α = β := (cancel_epi φ).mp (hα.trans hβ.symm)
  rw [hαβ]

/-- The `n`-fold fibre product of a universally open morphism with itself over the base,
presented by its universal property:  a scheme over the base carrying `n` morphisms to the
source, universally so, and again universally open over the base. -/
private lemma exists_universallyOpen_fiberPower
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyOpen f] (n : ℕ) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S) (a : Fin n → (P ⟶ X)),
      UniversallyOpen p ∧ (∀ i, a i ≫ f = p) ∧
      ∀ (Z : Scheme.{u}) (b : Z ⟶ S) (t : Fin n → (Z ⟶ X)),
        (∀ i, t i ≫ f = b) → ∃ l : Z ⟶ P, l ≫ p = b ∧ ∀ i, l ≫ a i = t i := by
  induction n with
  | zero =>
    refine ⟨S, 𝟙 S, Fin.elim0, inferInstance, (fun i => Fin.elim0 i), ?_⟩
    intro Z b t _
    exact ⟨b, Category.comp_id _, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨P, p, a, hp, ha, hl⟩ := ih
    have := hp
    let q : pullback f p ⟶ S := pullback.snd f p ≫ p
    let a' : Fin (n + 1) → (pullback f p ⟶ X) :=
      Fin.cases (pullback.fst f p) (fun i => pullback.snd f p ≫ a i)
    refine ⟨pullback f p, q, a', inferInstance, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact pullback.condition
      · dsimp [a', q]
        rw [Category.assoc, ha]
    · intro Z b t ht
      obtain ⟨l, hlp, hla⟩ := hl Z b (fun i => t i.succ) (fun i => ht i.succ)
      let m : Z ⟶ pullback f p := pullback.lift (t 0) l ((ht 0).trans hlp.symm)
      refine ⟨m, ?_, ?_⟩
      · dsimp [q, m]
        rw [pullback.lift_snd_assoc, hlp]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact pullback.lift_fst _ _ _
        · show m ≫ pullback.snd f p ≫ a j = t j.succ
          rw [show m ≫ pullback.snd f p ≫ a j = l ≫ a j from
            pullback.lift_snd_assoc _ _ _ _, hla]

/-- A point of a scheme with values in a field lifts through a closed immersion as soon as its
image lies in the range of that immersion. -/
private lemma exists_lift_of_isClosedImmersion
    {K : Type u} [Field K] {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (a : Spec (.of K) ⟶ Y) (ha : a (IsLocalRing.closedPoint K) ∈ Set.range i) :
    ∃ b : Spec (.of K) ⟶ X, b ≫ i = a := by
  let q := pullback.snd i a
  have : Surjective q := ⟨fun z => by
    have hz : a z ∈ Set.range i := (Subsingleton.elim z (IsLocalRing.closedPoint K)) ▸ ha
    show z ∈ Set.range q
    rw [show Set.range q = a ⁻¹' Set.range i from Scheme.Pullback.range_snd i a]
    exact hz⟩
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  refine ⟨inv q ≫ pullback.fst i a, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact IsIso.inv_hom_id_assoc q a

/-- A point of `X ×_S X` with values in a field lies on the diagonal exactly when its two
projections to `X` agree, provided `X ⟶ S` is separated. -/
private lemma mem_range_diagonal_iff
    {K : Type u} [Field K] {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (a : Spec (.of K) ⟶ pullback f f) :
    a (IsLocalRing.closedPoint K) ∈ Set.range (pullback.diagonal f) ↔
      a ≫ pullback.fst f f = a ≫ pullback.snd f f := by
  constructor
  · intro ha
    obtain ⟨b, rfl⟩ := exists_lift_of_isClosedImmersion (pullback.diagonal f) a ha
    rw [Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  · intro ha
    have he : (a ≫ pullback.fst f f) ≫ pullback.diagonal f = a := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, ha]
    exact ⟨(a ≫ pullback.fst f f) (IsLocalRing.closedPoint K),
      congrArg (fun b : Spec (.of K) ⟶ pullback f f => b (IsLocalRing.closedPoint K)) he⟩

/-- The number of connected components of a base change of `f` to a separably closed field is the
number of geometric connected components of the fibre of `f` at the image point. -/
@[ega "III 4.3.4" "partial"]
private lemma enatCard_connectedComponents_pullback_eq
    {K : Type u} [Field K] [IsSepClosed K] {X S : Scheme.{u}}
    (f : X ⟶ S) (a : Spec (.of K) ⟶ S) :
    ENat.card (_root_.ConnectedComponents (pullback (C := Scheme) f a)) =
      numGeometricConnectedComponents f (a (IsLocalRing.closedPoint K)) := by
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective a
  show ENat.card (_root_.ConnectedComponents
    (pullback (C := Scheme) f (Spec.map φ ≫ S.fromSpecResidueField s))) = _
  let : Algebra (S.residueField s) K := φ.hom.toAlgebra
  have he := enatCard_connectedComponents_iso
    (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) (Spec.map φ))
  have h := enatCard_connectedComponents_fiberBaseChange f s K
  have hp : (Spec.map φ ≫ S.fromSpecResidueField s) (IsLocalRing.closedPoint K) = s :=
    S.fromSpecResidueField_apply s _
  show _ = numGeometricConnectedComponents f
    ((Spec.map φ ≫ S.fromSpecResidueField s) (IsLocalRing.closedPoint K))
  rw [hp]
  exact he.symm.trans h

/-- In a totally disconnected space the connected components are the points. -/
private lemma enatCard_connectedComponents_of_totallyDisconnected
    (X : Type*) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    ENat.card (_root_.ConnectedComponents X) = ENat.card X := by
  refine (ENat.card_congr (Equiv.ofBijective (_root_.ConnectedComponents.mk : X → _)
    ⟨?_, _root_.ConnectedComponents.surjective_coe⟩)).symm
  intro x y h
  simpa only [ConnectedComponents.coe_eq_coe, connectedComponent_eq_singleton,
    Set.singleton_eq_singleton_iff] using h

/-- A type of cardinality at least `n` contains `n` distinct elements. -/
private lemma exists_injective_fin_of_le_enatCard {X : Type u} (n : ℕ)
    (h : (n : ℕ∞) ≤ ENat.card X) : ∃ a : Fin n → X, Function.Injective a := by
  have hn : (n : Cardinal) ≤ Cardinal.mk X := by
    simpa only [ENat.card, Cardinal.natCast_le_toENat] using h
  have hn' : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ Cardinal.lift.{0} (Cardinal.mk X) := by
    simpa only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast,
      Cardinal.lift_id'] using hn
  obtain ⟨a⟩ := Cardinal.lift_mk_le'.mp hn'
  exact ⟨a, a.injective⟩

/-- A morphism whose composition with a preceding surjection is universally open is itself
universally open:  a base change of the composition is the base change of the morphism
precomposed with a surjection, and an open map that factors through a surjective continuous map
makes the second factor open. -/
theorem universallyOpen_of_surjective_comp
    {X T S : Scheme.{u}} (h : X ⟶ T) (g : T ⟶ S)
    [Surjective h] [UniversallyOpen (h ≫ g)] : UniversallyOpen g := by
  refine ⟨CategoryTheory.MorphismProperty.universally_mk' _ _ (fun {S'} b _ => ?_)⟩
  let h' := pullback.snd h (pullback.fst g b)
  let g' := pullback.snd g b
  let e := pullbackRightPullbackFstIso g b h
  have he : h' ≫ g' = e.hom ≫ pullback.snd (h ≫ g) b :=
    (pullbackRightPullbackFstIso_hom_snd g b h).symm
  have hopen : IsOpenMap (h' ≫ g') := by
    rw [he]
    exact (pullback.snd (h ≫ g) b).isOpenMap.comp e.hom.isOpenMap
  have hsnd : IsOpenMap (pullback.snd g b) :=
    IsOpenMap.of_comp h'.continuous h'.surjective hopen
  have he' : (pullbackSymmetry b g).hom ≫ pullback.snd g b = pullback.fst b g :=
    pullbackSymmetry_hom_comp_snd b g
  rw [← he']
  exact hsnd.comp (pullbackSymmetry b g).hom.isOpenMap

/-- For a morphism integral over a separably closed field's base change, the points of the fibre
are counted by the geometric connected components of the fibre at the image point. -/
private lemma enatCard_pullback_eq_numGeometricConnectedComponents
    {K : Type u} [Field K] [IsSepClosed K] {T S : Scheme.{u}} (g : T ⟶ S) [IsIntegralHom g]
    (b : Spec (.of K) ⟶ S) :
    ENat.card (pullback (C := Scheme) g b) =
      numGeometricConnectedComponents g (b (IsLocalRing.closedPoint K)) := by
  have : TotallyDisconnectedSpace (pullback (C := Scheme) g b) :=
    totallyDisconnectedSpace_of_isIntegralHom_over_field (pullback.snd g b)
  rw [← enatCard_connectedComponents_of_totallyDisconnected,
    enatCard_connectedComponents_pullback_eq]

/-- For an integral, universally open morphism the locus where the fibres have at least `n`
geometric connected components is open.

The geometric fibres are totally disconnected, so the count is the number of points of a
geometric fibre;  `n` of them give a point of the `n`-fold fibre power lying in the open locus
where the `n` tautological morphisms are pairwise distinct, and the image of that locus in the
base is open. -/
@[ega "IV 15.5.4" "special case", ega "IV 15.5.9" "special case"]
theorem isOpen_le_numGeometricConnectedComponents_of_isIntegralHom
    {T S : Scheme.{u}} (g : T ⟶ S) [IsIntegralHom g] [UniversallyOpen g] (n : ℕ) :
    IsOpen {s | (n : ℕ∞) ≤ numGeometricConnectedComponents g s} := by
  classical
  obtain ⟨P, p, a, hp, ha, hl⟩ := exists_universallyOpen_fiberPower g n
  have := hp
  let d (i j : Fin n) : P ⟶ pullback g g :=
    pullback.lift (a i) (a j) ((ha i).trans (ha j).symm)
  let W : Set P := {w | ∀ i j : Fin n, i ≠ j → d i j w ∉ Set.range (pullback.diagonal g)}
  have hW : IsOpen W := by
    have hW_eq : W = ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
        (d i j) ⁻¹' (Set.range (pullback.diagonal g))ᶜ := by
      ext w
      simp only [W, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
    rw [hW_eq]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => ?_
    exact (pullback.diagonal g).isClosedEmbedding.isClosed_range.isOpen_compl.preimage
      (d i j).continuous
  have hwiff (K : Type u) [Field K] (l : Spec (.of K) ⟶ P) :
      l (IsLocalRing.closedPoint K) ∈ W ↔ Function.Injective (fun i => l ≫ a i) := by
    constructor
    · intro hw i j heq
      by_contra hij
      refine hw i j hij ((mem_range_diagonal_iff g (l ≫ d i j)).mpr ?_)
      show (l ≫ pullback.lift (a i) (a j) _) ≫ pullback.fst g g =
        (l ≫ pullback.lift (a i) (a j) _) ≫ pullback.snd g g
      rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_snd]
      exact heq
    · intro hinj i j hij hdiag
      refine hij (hinj ?_)
      have heq := (mem_range_diagonal_iff g (l ≫ d i j)).mp hdiag
      change (l ≫ pullback.lift (a i) (a j) _) ≫ pullback.fst g g =
        (l ≫ pullback.lift (a i) (a j) _) ≫ pullback.snd g g at heq
      rwa [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_snd] at heq
  have hbound : p '' W ⊆ {s | (n : ℕ∞) ≤ numGeometricConnectedComponents g s} := by
    rintro _ ⟨w, hw, rfl⟩
    let K := SeparableClosure (P.residueField w)
    let l : Spec (.of K) ⟶ P :=
      Spec.map (CommRingCat.ofHom (algebraMap (P.residueField w) K)) ≫
        P.fromSpecResidueField w
    have hlw : l (IsLocalRing.closedPoint K) = w := P.fromSpecResidueField_apply w _
    have hinj : Function.Injective (fun i => l ≫ a i) := (hwiff K l).mp (hlw.symm ▸ hw)
    let b := l ≫ p
    let r (i : Fin n) : Spec (.of K) ⟶ pullback g b :=
      pullback.lift (l ≫ a i) (𝟙 _) (by rw [Category.assoc, ha, Category.id_comp])
    have hr (i) : r i ≫ pullback.snd g b = 𝟙 _ := pullback.lift_snd _ _ _
    have hinj' : Function.Injective (fun i => r i (IsLocalRing.closedPoint K)) := by
      intro i j hij
      have heq := sections_ext_of_apply_eq (pullback.snd g b) (hr i) (hr j) hij
      refine hinj ?_
      have heq' := congrArg (fun r : Spec (.of K) ⟶ pullback g b =>
        r ≫ pullback.fst g b) heq
      simpa only [r, pullback.lift_fst] using heq'
    have hcard := ENat.card_le_card_of_injective hinj'
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      enatCard_pullback_eq_numGeometricConnectedComponents g b] at hcard
    have hb : b (IsLocalRing.closedPoint K) = p w := congrArg p hlw
    show (n : ℕ∞) ≤ numGeometricConnectedComponents g (p w)
    rwa [hb] at hcard
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hmem : s ∈ p '' W := by
    let K := AlgebraicClosure (S.residueField s)
    let b : Spec (.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
        S.fromSpecResidueField s
    have hb : b (IsLocalRing.closedPoint K) = s := S.fromSpecResidueField_apply s _
    have hcard : (n : ℕ∞) ≤ ENat.card (pullback (C := Scheme) g b) := by
      rw [enatCard_pullback_eq_numGeometricConnectedComponents g b, hb]
      exact hs
    obtain ⟨z, hz⟩ := exists_injective_fin_of_le_enatCard n hcard
    choose t ht htz using fun i =>
      exists_section_of_isIntegralHom_over_algClosed (pullback.snd g b) (z i)
    let t' (i : Fin n) := t i ≫ pullback.fst g b
    have ht' (i) : t' i ≫ g = b := by
      dsimp [t']
      rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
    have hinj : Function.Injective t' := by
      intro i j hij
      have hij' : t i = t j := by
        refine pullback.hom_ext hij ?_
        rw [ht, ht]
      refine hz ?_
      rw [← htz i, ← htz j, hij']
    obtain ⟨l, hlp, hla⟩ := hl (Spec (.of K)) b t' ht'
    refine ⟨l (IsLocalRing.closedPoint K), (hwiff K l).mpr ?_, ?_⟩
    · intro i j hij
      refine hinj ?_
      change l ≫ a i = l ≫ a j at hij
      rwa [hla, hla] at hij
    · exact (congrArg (fun b : Spec (.of K) ⟶ S => b (IsLocalRing.closedPoint K)) hlp).trans hb
  exact Filter.mem_of_superset ((p.isOpenMap W hW).mem_nhds hmem) hbound

/-- For an integral, universally open morphism the number of geometric connected components of
the fibres is lower semicontinuous on the target. -/
@[ega "IV 15.5.4" "special case"]
theorem lowerSemicontinuous_numGeometricConnectedComponents_of_isIntegralHom
    {T S : Scheme.{u}} (g : T ⟶ S) [IsIntegralHom g] [UniversallyOpen g] :
    LowerSemicontinuous (numGeometricConnectedComponents g) := by
  refine lowerSemicontinuous_iff_isOpen_preimage.mpr fun c => ?_
  induction c using ENat.recTopCoe with
  | top =>
    simp only [Set.Ioi_top, Set.preimage_empty]
    exact isOpen_empty
  | coe c =>
    have heq : numGeometricConnectedComponents g ⁻¹' Set.Ioi (c : ℕ∞) =
        {s | ((c + 1 : ℕ) : ℕ∞) ≤ numGeometricConnectedComponents g s} := by
      ext s
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one,
        ENat.natCast_add_one_le_iff]
    rw [heq]
    exact isOpen_le_numGeometricConnectedComponents_of_isIntegralHom g (c + 1)

/-- The fibres of a proper morphism have the same number of geometric connected components as
the fibres of the second map of its Stein factorization, since the first map has geometrically
connected fibres ([Stacks, Tag 03H2]). -/
@[ega "III 4.3.4" "partial, special case"]
theorem numGeometricConnectedComponents_eq_fromNormalization {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] :
    numGeometricConnectedComponents f =
      numGeometricConnectedComponents f.fromNormalization := by
  have := Stacks.SteinFactorization.isProper_toNormalization f
  have := Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper f
  have : UniversallyClosed f.toNormalization := inferInstance
  have h := numGeometricConnectedComponents_comp_eq f.toNormalization f.fromNormalization
  rwa [Scheme.Hom.toNormalization_fromNormalization f] at h

/-- **[Stacks, Tag 0BUI].**  For a flat proper morphism of finite presentation, the number of
geometric connected components of the fibres is a lower semicontinuous function on the base.

The count is the `ℕ∞`-valued function of Tag 055F.  The proof is the source's:  the Stein
factorization `f = f.fromNormalization ∘ f.toNormalization` has a first factor with
geometrically connected fibres (Tag 03H2), so it does not change the count, and a second factor
that is integral and, as `f` is flat of finite presentation and `f.toNormalization` is
surjective, universally open. -/
@[stacks 0BUI, ega "IV 15.5.4" "Flat case", ega "IV 15.5.9"]
theorem lowerSemicontinuous_numGeometricConnectedComponents {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    LowerSemicontinuous (numGeometricConnectedComponents f) := by
  have := Stacks.SteinFactorization.isProper_toNormalization f
  have hsurj : Surjective f.toNormalization :=
    Stacks.SteinFactorization.surjective_toNormalization f
  have hcomp : f.toNormalization ≫ f.fromNormalization = f :=
    Scheme.Hom.toNormalization_fromNormalization f
  have : UniversallyOpen (f.toNormalization ≫ f.fromNormalization) :=
    hcomp.symm ▸ (inferInstance : UniversallyOpen f)
  have : UniversallyOpen f.fromNormalization :=
    universallyOpen_of_surjective_comp f.toNormalization f.fromNormalization
  rw [numGeometricConnectedComponents_eq_fromNormalization f]
  exact lowerSemicontinuous_numGeometricConnectedComponents_of_isIntegralHom _

end AlgebraicGeometry

end
