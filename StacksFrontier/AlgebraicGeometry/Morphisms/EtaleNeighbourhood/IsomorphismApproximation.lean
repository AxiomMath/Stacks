module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FromCompletionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.CompletionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationScheme
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness
public import StacksFrontier.RingTheory.AdicCompletion.EndomorphismCongruentToIdentity
public import StacksFrontier.RingTheory.AdicCompletion.FlatLocalSquare
public import StacksCore.Tactic.StacksAttribute

/-!
# Approximating an isomorphism of completed local rings

Let `S` be a locally Noetherian scheme, let `X` and `Y` be locally of finite type over `S`, and
let `x ∈ X` and `y ∈ Y` lie over the same point of `S`, whose local ring is a G-ring. Given an
isomorphism `𝒪^∧_{Y, y} ≅ 𝒪^∧_{X, x}` of `𝒪_{S, s}`-algebras, there is for every `N ≥ 1` a
single pointed scheme `(U, u)` sitting in a diagram `(X, x) ← (U, u) → (Y, y)` over `S` in which
*both* arrows are elementary étale neighbourhoods, and over which the triangle of completed
local rings commutes modulo `𝔪_u ^ N`. This is Stacks 37.39.2, Tag 0CAV.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.along`: the other leg of such a diagram, read as an étale
  neighbourhood of its own target.
* `exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv`, in the namespace
  `StacksDraft.ArtinApproximation`: Tag 0CAV.

## Implementation notes

Tag 0CAU supplies the neighbourhood `(U, u)` of `(X, x)` together with a morphism `F : U → Y`
over `S`; all the work of 0CAV is to see that `F` is étale at `u`, and the route to that is to
show the induced map `𝒪^∧_{Y, y} → 𝒪^∧_{U, u}` is an isomorphism.

Two choices depart from the source. First, the source deduces étaleness from smoothness
(Tag 02HX) together with unramifiedness (Tag 02GK); here the isomorphism of completions gives
étaleness directly through Tag 039M, by
`RingHom.isEtaleLocalHom_of_bijective_adicCompletionMap`, which is shorter and avoids the
smoothness detour. Second, where the source argues with the graded rings `Gr_𝔪(R)` and a snake
lemma induction, the same conclusion is reached from first-order rigidity: the map in question
agrees modulo `𝔪_u ^ 2` with a composite of isomorphisms, and an endomorphism of a complete
Noetherian local ring that is the identity to first order is bijective
(`bijective_of_sub_id_mem_maximalIdeal_sq`). This is why `N` is replaced by `max N 2`.

The congruence that 0CAU provides holds on the image of the local ring `𝒪_{Y, y}`; it is
propagated to the whole completion by `sub_mem_of_apply_algebraMap_sub_mem`, which is what lets
the conclusion be stated for every element of `𝒪^∧_{Y, y}`, as the source's diagram of complete
local rings asserts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace AlgebraicGeometry.EtaleNeighborhood

/-- A second étale structure morphism on the pointed scheme underlying an étale neighbourhood
`U` of `(X, x)`, read as an étale neighbourhood of its own target: the other leg of a diagram
`(X, x) ← (U, u) → (Y, y)`. -/
def along {X Y : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x) {y : Y}
    (q : U.scheme ⟶ Y) (hqEt : Etale q) (hq : q U.point = y) : EtaleNeighborhood Y y where
  scheme := U.scheme
  point := U.point
  toBase := q
  etale_toBase := hqEt
  map_point := hq

/-- The scheme of `U.along q hqEt hq` is the scheme of `U`. -/
@[simp]
lemma along_scheme {X Y : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x) {y : Y}
    (q : U.scheme ⟶ Y) (hqEt : Etale q) (hq : q U.point = y) :
    (U.along q hqEt hq).scheme = U.scheme := rfl

/-- The point of `U.along q hqEt hq` is the point of `U`. -/
@[simp]
lemma along_point {X Y : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x) {y : Y}
    (q : U.scheme ⟶ Y) (hqEt : Etale q) (hq : q U.point = y) :
    (U.along q hqEt hq).point = U.point := rfl

/-- The structure morphism of `U.along q hqEt hq` is `q`. -/
@[simp]
lemma along_toBase {X Y : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x) {y : Y}
    (q : U.scheme ⟶ Y) (hqEt : Etale q) (hq : q U.point = y) :
    (U.along q hqEt hq).toBase = q := rfl

/-- The map of local rings induced by a morphism carrying `u` to `y`, read as a map out of the
local ring at `y`. This is the spelling in which Tag 0CAU states its congruence. -/
abbrev _root_.AlgebraicGeometry.Scheme.Hom.stalkHomAt {U Y : Scheme.{u}} {u : U} {y : Y}
    (q : U ⟶ Y) (hq : q u = y) : Y.presheaf.stalk y →+* U.presheaf.stalk u :=
  ((Y.presheaf.stalkCongr (.of_eq hq.symm)).hom ≫ q.stalkMap u).hom

/-- The induced map on completed local rings of a morphism carrying `u` to `y`. -/
def _root_.AlgebraicGeometry.Scheme.Hom.completionMapAt {U Y : Scheme.{u}} {u : U} {y : Y}
    (q : U ⟶ Y) (hq : q u = y) :
    AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) →+*
      AdicCompletion (maximalIdeal (U.presheaf.stalk u)) (U.presheaf.stalk u) :=
  adicCompletionMap (q.stalkHomAt hq) (maximalIdeal (Y.presheaf.stalk y))
    (maximalIdeal (U.presheaf.stalk u)) (IsLocalRing.map_maximalIdeal_le _)

/-- The induced map of local rings of a composite factors through the intermediate point. This
is what transports a congruence in the completed local ring along a restriction. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.stalkHomAt_comp {Z U Y : Scheme.{u}}
    {z : Z} {u : U} {y : Y} (a : Z ⟶ U) (b : U ⟶ Y) (ha : a z = u) (hb : b u = y) :
    (a ≫ b).stalkHomAt (by subst ha; exact hb) = (a.stalkHomAt ha).comp (b.stalkHomAt hb) := by
  subst ha
  subst hb
  rw [← CommRingCat.hom_comp]
  refine congrArg CommRingCat.Hom.hom ?_
  simp only [Scheme.Hom.stalkMap_comp, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  change Y.presheaf.stalkSpecializes (specializes_refl (b (a z))) ≫
      Scheme.Hom.stalkMap b (a z) ≫ Scheme.Hom.stalkMap a z = _
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- The map of local rings induced by the structure morphism of an étale neighbourhood. -/
abbrev stalkHom {X : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x) :
    X.presheaf.stalk x →+* U.scheme.presheaf.stalk U.point :=
  U.toBase.stalkHomAt U.map_point

/-- Restricting an étale neighbourhood along a further étale neighbourhood of its point
composes the induced maps of local rings. A corollary of
`AlgebraicGeometry.Scheme.Hom.stalkHomAt_comp`; the two proofs of the composite's point
equality agree by proof irrelevance. -/
theorem stalkHom_comp {X : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x)
    (V : EtaleNeighborhood U.scheme U.point) :
    (U.comp V).stalkHom = V.stalkHom.comp U.stalkHom :=
  Scheme.Hom.stalkHomAt_comp V.toBase U.toBase V.map_point U.map_point

/-- The induced map on completed local rings of an étale neighbourhood. -/
abbrev completionMap {X : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x) :
    AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+*
      AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
        (U.scheme.presheaf.stalk U.point) :=
  U.toBase.completionMapAt U.map_point

end AlgebraicGeometry.EtaleNeighborhood

namespace StacksDraft.ArtinApproximation

/-- A bijective local homomorphism of local rings induces a bijection of residue fields: the
induced map is a homomorphism of fields, hence injective, and it is surjective because the map
and the residue map both are. -/
private theorem bijective_residueFieldMap_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hf : Function.Bijective f) :
    Function.Bijective (ResidueField.map f) := by
  refine ⟨(ResidueField.map f).injective, fun z => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective z
  obtain ⟨a, rfl⟩ := hf.surjective b
  exact ⟨residue A a, ResidueField.map_residue f a⟩

/-- Étaleness of the local homomorphism at a point is unaffected by transporting the source
along an equality of points. -/
theorem isEtaleLocalHom_stalkCongr_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Y} (hy : f x = y)
    (hEt : IsEtaleAt f x) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    RingHom.IsEtaleLocalHom
      (((Y.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap x).hom) := by
  subst hy
  simpa using hEt

/-- A congruence modulo `𝔪_B ^ M` between elements of the completion of `B` pushes forward,
along the completion of a local homomorphism `B → C`, to a congruence modulo `𝔪_C ^ N` for any
`N ≤ M`. -/
theorem adicCompletionMap_mem_map_maximalIdeal_pow {B C : Type u} [CommRing B]
    [CommRing C] [IsLocalRing B] [IsLocalRing C] [IsNoetherianRing B] [IsNoetherianRing C]
    (e : B →+* C) [IsLocalHom e] {M N : ℕ} (hNM : N ≤ M)
    {v : AdicCompletion (maximalIdeal B) B}
    (hv : v ∈ Ideal.map (algebraMap B (AdicCompletion (maximalIdeal B) B)) (maximalIdeal B ^ M)) :
    adicCompletionMap e (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le e) v ∈
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ N) := by
  have h : Ideal.map (adicCompletionMap e (maximalIdeal B) (maximalIdeal C)
        (map_maximalIdeal_le e))
      (Ideal.map (algebraMap B (AdicCompletion (maximalIdeal B) B)) (maximalIdeal B ^ M)) ≤
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ N) := by
    rw [Ideal.map_map, adicCompletionMap_comp_algebraMap e (maximalIdeal B)
      (maximalIdeal C) (map_maximalIdeal_le e), ← Ideal.map_map]
    refine Ideal.map_mono ?_
    rw [Ideal.map_pow]
    exact (Ideal.pow_right_mono (map_maximalIdeal_le e) M).trans (Ideal.pow_le_pow_right hNM)
  exact h (Ideal.mem_map_of_mem _ hv)

/-- The completion of a local homomorphism that factors as `g ∘ f` is the composite of the
completions. -/
private theorem adicCompletionMap_eq_comp_of_eq_comp {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] (f : A →+* B) (g : B →+* C)
    (h : A →+* C) (hf : (maximalIdeal A).map f ≤ maximalIdeal B)
    (hg : (maximalIdeal B).map g ≤ maximalIdeal C)
    (hh : (maximalIdeal A).map h ≤ maximalIdeal C) (hgf : h = g.comp f) :
    adicCompletionMap h (maximalIdeal A) (maximalIdeal C) hh =
      (adicCompletionMap g (maximalIdeal B) (maximalIdeal C) hg).comp
        (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) hf) := by
  rw [adicCompletionMap_comp_adicCompletionMap _ _ _ _ _ hf hg (hgf ▸ hh)]
  exact adicCompletionMap_congr _ _ _ _ hgf

/-- **The ring-theoretic heart of Tag 0CAV.** Let `p : B → C` and `r : A → C` be local
homomorphisms of Noetherian local rings, let `Φ : A^∧ ≃ B^∧` be an isomorphism of completions,
and suppose the completion `p^∧` of `p` is bijective. If `p^∧ ∘ Φ` and `r^∧` agree modulo
`𝔪_C ^ M` on the image of `A`, with `M ≥ 2`, then they agree modulo `𝔪_C ^ M` everywhere, and
`r^∧` is itself bijective.

Both halves come from the same observation. The congruence spreads from the image of `A` to the
whole of `A^∧` because `A` is dense in `A^∧` modulo any power of the maximal ideal
(`sub_mem_of_apply_algebraMap_sub_mem`). Given that, `(p^∧ ∘ Φ)⁻¹ ∘ r^∧` is an endomorphism of
`A^∧` agreeing with the identity modulo `𝔪 ^ 2`, hence bijective
(`bijective_of_sub_id_mem_maximalIdeal_sq`); so `r^∧`, a composite of two bijections, is
bijective. This replaces the source's graded-ring computation. -/
private theorem congr_and_bijective_adicCompletionMap {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (p : B →+* C) [IsLocalHom p] (r : A →+* C) [IsLocalHom r]
    (Φ : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B)
    (hp : Function.Bijective
      (adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p)))
    (M : ℕ) (h2M : 2 ≤ M)
    (hbase : ∀ a : A,
      adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p)
          (Φ (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) -
        algebraMap C (AdicCompletion (maximalIdeal C) C) (r a) ∈
          Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M)) :
    (∀ z : AdicCompletion (maximalIdeal A) A,
        adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p) (Φ z) -
          adicCompletionMap r (maximalIdeal A) (maximalIdeal C) (map_maximalIdeal_le r) z ∈
            Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M)) ∧
      Function.Bijective
        (adicCompletionMap r (maximalIdeal A) (maximalIdeal C) (map_maximalIdeal_le r)) := by
  set pC := adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p)
    with hpC
  set qC := adicCompletionMap r (maximalIdeal A) (maximalIdeal C) (map_maximalIdeal_le r)
    with hqC
  have hpCloc : IsLocalHom pC := AdicCompletion.isLocalHom_adicCompletionMap p
  have hrbase : (adicCompletionMap r (maximalIdeal A) (maximalIdeal C)
        (map_maximalIdeal_le r)).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap C (AdicCompletion (maximalIdeal C) C)).comp r :=
    adicCompletionMap_comp_algebraMap r (maximalIdeal A) (maximalIdeal C)
      (map_maximalIdeal_le r)
  have hqCbase : ∀ a : A, qC (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap C (AdicCompletion (maximalIdeal C) C) (r a) := by
    intro a
    rw [hqC]
    exact RingHom.congr_fun hrbase a
  have hKmax : Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M) =
      maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ M := by
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map]
  have h₂ : Ideal.map qC (Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A))
      (maximalIdeal A ^ M)) ≤
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M) :=
    Ideal.map_le_iff_le_comap.mpr fun _ hv =>
      adicCompletionMap_mem_map_maximalIdeal_pow r le_rfl hv
  have h₁ : Ideal.map (pC.comp Φ.toRingHom) (Ideal.map
      (algebraMap A (AdicCompletion (maximalIdeal A) A)) (maximalIdeal A ^ M)) ≤
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M) :=
    calc Ideal.map (pC.comp Φ.toRingHom)
            (Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) (maximalIdeal A ^ M))
        = Ideal.map pC (Ideal.map Φ.toRingHom
            (Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A))
              (maximalIdeal A ^ M))) := (Ideal.map_map _ _).symm
      _ = Ideal.map pC (Ideal.map Φ.toRingHom
            (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ M)) := by
            rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map]
      _ = Ideal.map pC (maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ M) := by
            rw [Ideal.map_pow, map_maximalIdeal_of_surjective Φ.toRingHom Φ.surjective]
      _ ≤ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ M := by
            rw [Ideal.map_pow]
            exact Ideal.pow_right_mono (map_maximalIdeal_le pC) M
      _ = _ := hKmax.symm
  have hcong : ∀ z : AdicCompletion (maximalIdeal A) A, pC (Φ z) - qC z ∈
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C))
        (maximalIdeal C ^ M) := fun z =>
    sub_mem_of_apply_algebraMap_sub_mem (maximalIdeal A) (IsNoetherian.noetherian _) M _
      (pC.comp Φ.toRingHom) qC (fun a => by rw [RingHom.comp_apply, hqCbase a]; exact hbase a)
      h₁ h₂ z
  refine ⟨hcong, ?_⟩
  have hτbij : Function.Bijective (pC.comp Φ.toRingHom) := by
    rw [RingHom.coe_comp]
    exact hp.comp Φ.bijective
  set τe := RingEquiv.ofBijective (pC.comp Φ.toRingHom) hτbij with hτe
  have hτeapp : ∀ z, τe z = pC (Φ z) := fun z => rfl
  have hψ : ∀ w : AdicCompletion (maximalIdeal A) A, (τe.symm.toRingHom.comp qC) w - w ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ 2 := by
    intro w
    have hw : (τe.symm.toRingHom.comp qC) w - w = τe.symm (qC w - τe w) := by
      rw [map_sub, τe.symm_apply_apply]
      rfl
    have hmem : qC w - τe w ∈ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ 2 := by
      have hz := hcong w
      rw [hKmax] at hz
      have hneg : qC w - τe w = -(pC (Φ w) - qC w) := by rw [hτeapp w]; ring
      rw [hneg]
      exact Ideal.pow_le_pow_right h2M (neg_mem hz)
    rw [hw]
    have : IsLocalHom τe.symm.toRingHom :=
      isLocalHom_of_leftInverse τe.toRingHom τe.apply_symm_apply
    refine Ideal.pow_right_mono (map_maximalIdeal_le τe.symm.toRingHom) 2 ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hmem
  have hψbij : Function.Bijective (τe.symm.toRingHom.comp qC) :=
    bijective_of_sub_id_mem_maximalIdeal_sq _ _ hψ
  have hfun : ⇑qC = ⇑(pC.comp Φ.toRingHom) ∘ ⇑(τe.symm.toRingHom.comp qC) :=
    funext fun w => (τe.apply_symm_apply (qC w)).symm
  rw [hfun]
  exact hτbij.comp hψbij

/-- Bijectivity of the residue field map of the local homomorphism at a point, transported along
an equality of points, is isomorphy of the residue field map of the morphism. -/
theorem bijective_residueField_map_stalkHomAt_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) {y : Y} (hy : f x = y) :
    Function.Bijective (ResidueField.map (f.stalkHomAt hy)) ↔
      IsIso (f.residueFieldMap x) := by
  subst hy
  simp only [Scheme.Hom.stalkHomAt, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rw [ConcreteCategory.isIso_iff_bijective]
  rfl

/-- The local homomorphism at a point of a morphism locally of finite type is essentially of
finite type, in the spelling transported along an equality of points. -/
private theorem essFiniteType_stalkCongr_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [LocallyOfFiniteType f] {y : Y} (hy : f x = y) :
    RingHom.EssFiniteType
      (((Y.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap x).hom) := by
  subst hy
  simpa using LocallyOfFiniteType.stalkMap f x

/-- Converse transport to `StacksDraft.ArtinApproximation.isEtaleLocalHom_stalkCongr_comp`:
étaleness of the transported local homomorphism gives étaleness of the morphism at the point. -/
private theorem isEtaleAt_of_isEtaleLocalHom_stalkCongr_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Y} (hy : f x = y)
    (h : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      RingHom.IsEtaleLocalHom
        (((Y.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap x).hom)) :
    IsEtaleAt f x := by
  subst hy
  simpa using h

/-- Restricting a morphism `f : Z ⟶ Y` along an étale neighbourhood `V` of a point `p` of `Z`
composes the induced maps of local rings. This is
`AlgebraicGeometry.EtaleNeighborhood.stalkHom_comp` for a morphism that is not assumed étale,
which is the form needed before `F` is known to be étale. -/
private theorem stalkHom_comp_of_eq {Y Z : Scheme.{u}} (f : Z ⟶ Y) {p : Z} {y : Y}
    (hy : f p = y) (V : EtaleNeighborhood Z p) (hc : (V.toBase ≫ f) V.point = y) :
    ((Y.presheaf.stalkCongr (.of_eq hc.symm)).hom ≫ (V.toBase ≫ f).stalkMap V.point).hom =
      V.stalkHom.comp (((Y.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap p).hom) := by
  subst hy
  rw [← CommRingCat.hom_comp]
  refine congrArg CommRingCat.Hom.hom ?_
  simp only [Scheme.Hom.stalkMap_comp, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ (Specializes.of_eq V.map_point) _

/-- The completion of the structure map of a composite étale neighbourhood factors as the
completion of the second stage after the completion of the first. -/
private theorem completionMap_comp {X : Scheme.{u}} {x : X} (U : EtaleNeighborhood X x)
    (V : EtaleNeighborhood U.scheme U.point) :
    (U.comp V).completionMap =
      (adicCompletionMap V.stalkHom (maximalIdeal (U.scheme.presheaf.stalk U.point))
        (maximalIdeal (V.scheme.presheaf.stalk V.point)) (map_maximalIdeal_le _)).comp
        U.completionMap := by
  exact adicCompletionMap_eq_comp_of_eq_comp _ _ _ _ _ _ (EtaleNeighborhood.stalkHom_comp U V)

/-- **Stacks Project, Tag 0CAV (More on Morphisms, Lemma 37.39.2).** Let `S` be a locally
Noetherian scheme, let `f : X ⟶ S` and `g : Y ⟶ S` be locally of finite type, and let `x ∈ X`
and `y ∈ Y` lie over a common point `s` of `S` whose local ring is a G-ring. Suppose given an
isomorphism `Φ : 𝒪^∧_{Y, y} ≅ 𝒪^∧_{X, x}` which is compatible with the two maps from
`𝒪_{S, s}`. Then for every `N ≥ 1` there is a single pointed scheme `(U, u)` sitting in a
diagram `(X, x) ← (U, u) → (Y, y)` over `S` in which *both* legs are elementary étale
neighbourhoods, and over which the triangle of completed local rings commutes modulo
`𝔪_u ^ N`: for every `z ∈ 𝒪^∧_{Y, y}`, the two images of `z` in `𝒪^∧_{U, u}` — one obtained by
transporting `z` through `Φ` and then along the first leg, the other by going directly along the
second leg — differ by an element of `𝔪_u ^ N · 𝒪^∧_{U, u}`.

Tag 0CAU already produces the neighbourhood `(U₀, u₀)` of `(X, x)` and a morphism `F : U₀ ⟶ Y`
over `S` whose congruence holds on the image of `𝒪_{Y, y}`. The content added here is that `F`
is étale at `u₀`, which is extracted from the congruence itself: it forces the induced map
`𝒪^∧_{Y, y} → 𝒪^∧_{U₀, u₀}` to be bijective, and a bijection of completions upgrades to
étaleness of local rings by Tag 039M. Shrinking `U₀` to an open on which `F` is étale gives the
required `(U, u)`.

The difference of the two completion maps is written with an explicit `HSub` instance because
the two completions are only definitionally, not reducibly, the same ring: the second is indexed
by the scheme of `EtaleNeighborhood.along`, whose `scheme` field is the first one by `rfl`. The
term is the ordinary `_ - _`. -/
@[stacks 0CAV "with NO carried hypotheses, exactly as Tag 0CAU it rests on: the only \
hypotheses are the source's own. Everything in the source's own proof of 37.39.2 \
is proved here. The congruence is stated on the whole completed local ring of the neighbourhood \
rather than only on the image of the local ring, which is what the source's diagram of complete \
local rings asserts"]
theorem exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (y : Y) (hxy : f x = g y)
    (hG : IsGRing (S.presheaf.stalk (f x)))
    (N : ℕ) (hN : 1 ≤ N)
    (Φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hΦ : Φ.toRingHom.comp ((algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
          ((S.presheaf.stalkCongr (.of_eq hxy)).hom ≫ g.stalkMap y).hom) =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (f.stalkMap x).hom) :
    ∃ (U : EtaleNeighborhood X x) (q : U.scheme ⟶ Y) (hqEt : Etale q) (hq : q U.point = y),
      U.IsElementary ∧ (U.along q hqEt hq).IsElementary ∧ q ≫ g = U.toBase ≫ f ∧
        ∀ z : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y),
          @HSub.hSub _ _ _ instHSub (U.completionMap (Φ z))
              ((U.along q hqEt hq).completionMap z) ∈
            Ideal.map (algebraMap (U.scheme.presheaf.stalk U.point)
              (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
                (U.scheme.presheaf.stalk U.point)))
              (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hNM : N ≤ max N 2 := le_max_left _ _
  have h2M : 2 ≤ max N 2 := le_max_right _ _
  have hΦloc : IsLocalHom Φ.toRingHom := isLocalHom_of_leftInverse Φ.symm.toRingHom Φ.left_inv
  have hφloc : IsLocalHom (Φ.toRingHom.comp (algebraMap (Y.presheaf.stalk y)
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))) :=
    inferInstance
  have hbase : (Φ.toRingHom.comp (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))).comp
        ((S.presheaf.stalkCongr (.of_eq hxy)).hom ≫ g.stalkMap y).hom =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (f.stalkMap x).hom := by
    rwa [RingHom.comp_assoc]
  obtain ⟨U₀, hU₀, F, hF, hover, happrox⟩ :=
    exists_elementaryEtaleNeighborhood_approximation f g x y hxy hG (max N 2)
      (hN.trans hNM) _ hφloc hbase
  let : IsLocallyNoetherian U₀.scheme := LocallyOfFiniteType.isLocallyNoetherian U₀.toBase
  have hpκ : Function.Bijective (ResidueField.map U₀.stalkHom) :=
    (bijective_residueField_map_stalkHomAt_iff U₀.toBase U₀.point U₀.map_point).mpr
      ((EtaleNeighborhood.isElementary_iff U₀).mp hU₀)
  have hpEt : RingHom.IsEtaleLocalHom U₀.stalkHom :=
    isEtaleLocalHom_stalkCongr_comp U₀.toBase U₀.point U₀.map_point
      ((etale_iff_forall_isEtaleAt U₀.toBase).mp inferInstance U₀.point)
  have hpCbij := RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom U₀.stalkHom hpEt hpκ
  obtain ⟨hcong, hqCbij⟩ := congr_and_bijective_adicCompletionMap U₀.stalkHom
    (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U₀.point).hom) Φ hpCbij
    (max N 2) h2M happrox
  have hFcomp : LocallyOfFiniteType (F ≫ g) := by rw [hover]; infer_instance
  have hFft : LocallyOfFiniteType F := locallyOfFiniteType_of_comp F g
  have hFat : EtaleAt F U₀.point :=
    (isEtaleAt_iff_etaleAt F U₀.point).mp
      (isEtaleAt_of_isEtaleLocalHom_stalkCongr_comp F U₀.point hF
        (RingHom.isEtaleLocalHom_of_bijective_adicCompletionMap _
          (essFiniteType_stalkCongr_comp F U₀.point hF) hqCbij))
  have hqSκ : Function.Bijective (ResidueField.map
      (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U₀.point).hom)) := by
    have hqCloc : IsLocalHom (adicCompletionMap
        (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U₀.point).hom)
        (maximalIdeal (Y.presheaf.stalk y))
        (maximalIdeal (U₀.scheme.presheaf.stalk U₀.point)) (map_maximalIdeal_le _)) :=
      AdicCompletion.isLocalHom_adicCompletionMap _
    have hκC := bijective_residueFieldMap_of_bijective _ hqCbij
    have hsq := AdicCompletion.residueField_adicCompletionMap_comp
      (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U₀.point).hom)
    refine (Function.Bijective.of_comp_iff' (AdicCompletion.residueField_map_bijective
      (U₀.scheme.presheaf.stalk U₀.point)) _).mp ?_
    rw [← RingHom.coe_comp, ← hsq, RingHom.coe_comp]
    exact hκC.comp (AdicCompletion.residueField_map_bijective (Y.presheaf.stalk y))
  have hFres : IsIso (F.residueFieldMap U₀.point) :=
    (bijective_residueField_map_stalkHomAt_iff F U₀.point hF).mp hqSκ
  obtain ⟨W, hWaff, hWmem, hWet⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt F U₀.point hFat
  obtain ⟨w, hw⟩ : ∃ w : W.toScheme, W.ι w = U₀.point := ⟨⟨U₀.point, hWmem⟩, rfl⟩
  let V : EtaleNeighborhood U₀.scheme U₀.point :=
    { scheme := W.toScheme
      point := w
      toBase := W.ι
      map_point := hw }
  have hVel : V.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact inferInstanceAs (IsIso (W.ι.residueFieldMap w))
  have hq : (W.ι ≫ F) (U₀.comp V).point = y := by
    change F (W.ι w) = y
    rwa [hw]
  refine ⟨U₀.comp V, W.ι ≫ F, hWet, hq, EtaleNeighborhood.IsElementary.comp hU₀ hVel, ?_, ?_, ?_⟩
  · rw [EtaleNeighborhood.isElementary_iff]
    change IsIso ((W.ι ≫ F).residueFieldMap w)
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' ((F.isIso_residueFieldMap_congr hw).mpr hFres) inferInstance
  · change (W.ι ≫ F) ≫ g = (W.ι ≫ U₀.toBase) ≫ f
    rw [Category.assoc, Category.assoc, hover]
  · intro z
    have hb : ((U₀.comp V).along (W.ι ≫ F) hWet hq).completionMap =
        (adicCompletionMap V.stalkHom (maximalIdeal (U₀.scheme.presheaf.stalk U₀.point))
          (maximalIdeal (V.scheme.presheaf.stalk V.point)) (map_maximalIdeal_le _)).comp
          (adicCompletionMap
            (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U₀.point).hom)
            (maximalIdeal (Y.presheaf.stalk y))
            (maximalIdeal (U₀.scheme.presheaf.stalk U₀.point)) (map_maximalIdeal_le _)) := by
      exact adicCompletionMap_eq_comp_of_eq_comp _ _ _ _ _ _ (stalkHom_comp_of_eq F hF V hq)
    have e1 : (U₀.comp V).completionMap (Φ z) =
        adicCompletionMap V.stalkHom (maximalIdeal (U₀.scheme.presheaf.stalk U₀.point))
          (maximalIdeal (V.scheme.presheaf.stalk V.point)) (map_maximalIdeal_le _)
          (U₀.completionMap (Φ z)) :=
      RingHom.congr_fun (completionMap_comp U₀ V) (Φ z)
    have e2 : ((U₀.comp V).along (W.ι ≫ F) hWet hq).completionMap z =
        adicCompletionMap V.stalkHom (maximalIdeal (U₀.scheme.presheaf.stalk U₀.point))
          (maximalIdeal (V.scheme.presheaf.stalk V.point)) (map_maximalIdeal_le _)
          (adicCompletionMap
            (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U₀.point).hom)
            (maximalIdeal (Y.presheaf.stalk y))
            (maximalIdeal (U₀.scheme.presheaf.stalk U₀.point)) (map_maximalIdeal_le _) z) :=
      RingHom.congr_fun hb z
    have hmem := adicCompletionMap_mem_map_maximalIdeal_pow V.stalkHom hNM (hcong z)
    rw [map_sub] at hmem
    rw [e1, e2]
    exact hmem

end StacksDraft.ArtinApproximation

end
