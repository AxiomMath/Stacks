module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction

/-!
# Transport of a bivariant class along an isomorphism of its source

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `v : A ⟶ W` and
`u : B ⟶ W` be morphisms of schemes locally of finite type over `S` and let `θ : A ≅ B` be an
isomorphism over `W`, that is, with `θ ≫ u = v`. Then `A^p(A ⟶ W) = A^p(B ⟶ W)`: a bivariant
class for `v` is carried to one for `u` by transporting its cap operations along the induced
isomorphisms `T ×_W A ≅ T ×_W B` of the base changes.

## Main definitions

* `Stacks.Chow.transportPullbackIso` — the isomorphism `T ×_W A ≅ T ×_W B` induced by `θ`.
* `Stacks.Chow.bivariantTransportCap` — the transported cap operation.
* `Stacks.Chow.bivariantTransport` — the transported bivariant class.
* `Stacks.Chow.bivariantTransportAddHom` — the transport as a homomorphism of groups.
* `Stacks.Chow.IsBivariantTransport` — the assertion that a bivariant class for `u` is the
  transport of a given class for `v`, namely that it caps by the transported operation.

## Main results

* `Stacks.Chow.bivariantTransportCap_proper_naturality`,
  `Stacks.Chow.bivariantTransportCap_flat_naturality`,
  `Stacks.Chow.bivariantTransportCap_gysin_naturality` — the three axioms of Stacks 0B76 for the
  transported cap operation.
* `Stacks.Chow.eq_of_isBivariantTransport` — the transport is determined by its cap operations.
* `Stacks.Chow.bivariantTransport_add`, `_neg`, `_zero` — transport is additive.

## Implementation notes

The hypotheses are exactly those of `Stacks.Chow.bivariantRestriction`, and for the same reasons:
the Gysin axiom cannot hold for an arbitrary `Stacks.Chow.GysinSystem` — the two cap operations
land on isomorphic but different schemes, and the first Chern class rules a system provides there
are unrelated data — so the construction carries
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, the isomorphism case of Stacks 02TA. See
the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction`.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The induced isomorphism of base changes -/

section Comparison

variable {A B W : Scheme.{u}} (v : A ⟶ W) (u : B ⟶ W) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)

/-- The isomorphism `T ×_W A ≅ T ×_W B` of base changes induced by an isomorphism `θ : A ≅ B`
over `W`. -/
def transportPullbackIso {T : Scheme.{u}} (g : T ⟶ W) : pullback v g ≅ pullback u g :=
  asIso (pullback.map v g u g θ.hom (𝟙 T) (𝟙 W) (by rw [Category.comp_id, hθ]) (by simp))

/-- The induced isomorphism of base changes lies over `θ` on the second factor. -/
@[reassoc (attr := simp)]
theorem transportPullbackIso_hom_fst {T : Scheme.{u}} (g : T ⟶ W) :
    (transportPullbackIso v u θ hθ g).hom ≫ pullback.fst u g = pullback.fst v g ≫ θ.hom := by
  simp [transportPullbackIso]

/-- The induced isomorphism of base changes lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem transportPullbackIso_hom_snd {T : Scheme.{u}} (g : T ⟶ W) :
    (transportPullbackIso v u θ hθ g).hom ≫ pullback.snd u g = pullback.snd v g := by
  simp [transportPullbackIso]

/-- The inverse of the induced isomorphism of base changes lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem transportPullbackIso_inv_snd {T : Scheme.{u}} (g : T ⟶ W) :
    (transportPullbackIso v u θ hθ g).inv ≫ pullback.snd v g = pullback.snd u g := by
  rw [Iso.inv_comp_eq, transportPullbackIso_hom_snd]

/-- The inverse of the induced isomorphism of base changes lies over `θ⁻¹` on the second
factor. -/
@[reassoc (attr := simp)]
theorem transportPullbackIso_inv_fst {T : Scheme.{u}} (g : T ⟶ W) :
    (transportPullbackIso v u θ hθ g).inv ≫ pullback.fst v g = pullback.fst u g ≫ θ.inv := by
  rw [Iso.inv_comp_eq, transportPullbackIso_hom_fst_assoc, Iso.hom_inv_id, Category.comp_id]

end Comparison

/-! ### The transported cap operation -/

section Transport

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
  (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
  (p : ℤ)

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
include hv hu hθ in
/-- An isomorphism over `W` of two morphisms to `W` is an isomorphism over the base. -/
theorem transport_comp_structureMorphism_eq : θ.hom ≫ sB = sA := by
  rw [← hu, ← Category.assoc, hθ, hv]

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
include hv hu hθ in
/-- The induced isomorphism of base changes is an isomorphism over the base. -/
theorem transportPullbackIso_hom_comp_base {T : Scheme.{u}} (g : T ⟶ W) :
    (transportPullbackIso v u θ hθ g).hom ≫ (pullback.fst u g ≫ sB) = pullback.fst v g ≫ sA := by
  rw [transportPullbackIso_hom_fst_assoc,
    transport_comp_structureMorphism_eq C sA sB sW v hv u hu θ hθ]

/-- The cap operation of the transport of a bivariant class `c` for `v : A ⟶ W` along an
isomorphism `θ : A ≅ B` over `W`: the cap operation of `c`, pushed forward along the induced
isomorphism of base changes. -/
def bivariantTransportCap (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (g : T ⟶ W)
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sW) k →+ chowGroup C (pullback.fst u g ≫ sB) (k - p) :=
  (chowPushforwardOfIso C (pullback.fst v g ≫ sA) (pullback.fst u g ≫ sB)
      (transportPullbackIso v u θ hθ g).hom
      (transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g) (k - p)).comp (c.cap g k)

omit [LocallyOfFiniteType u] in
/-- The cap operation of a transport, read on an element. -/
theorem bivariantTransportCap_apply (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}}
    (g : T ⟶ W) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sW) k) :
    bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k α =
      chowPushforwardOfIso C (pullback.fst v g ≫ sA) (pullback.fst u g ≫ sB)
        (transportPullbackIso v u θ hθ g).hom
        (transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g) (k - p)
        (c.cap g k α) :=
  rfl

/-! ### The base change of a morphism of test schemes, transported -/

/-- The base change of a morphism `h : T' ⟶ T` of test schemes to the base changes of `v`,
transported from a base change `h'` of `h` to those of `u`. -/
def transportBaseChange {T T' : Scheme.{u}} (g : T ⟶ W) (h : T' ⟶ T)
    (h' : pullback u (h ≫ g) ⟶ pullback u g) : pullback v (h ≫ g) ⟶ pullback v g :=
  (transportPullbackIso v u θ hθ (h ≫ g)).hom ≫ h' ≫ (transportPullbackIso v u θ hθ g).inv

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
/-- The transported base change is compatible with the projections to `A`. -/
theorem transportBaseChange_fst {T T' : Scheme.{u}} (g : T ⟶ W) (h : T' ⟶ T)
    (h' : pullback u (h ≫ g) ⟶ pullback u g)
    (hfst : h' ≫ pullback.fst u g = pullback.fst u (h ≫ g)) :
    transportBaseChange v u θ hθ g h h' ≫ pullback.fst v g = pullback.fst v (h ≫ g) := by
  simp [transportBaseChange, reassoc_of% hfst]

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
/-- The transported base change composed with the comparison isomorphism. -/
theorem transportBaseChange_comp_hom {T T' : Scheme.{u}} (g : T ⟶ W) (h : T' ⟶ T)
    (h' : pullback u (h ≫ g) ⟶ pullback u g) :
    transportBaseChange v u θ hθ g h h' ≫ (transportPullbackIso v u θ hθ g).hom =
      (transportPullbackIso v u θ hθ (h ≫ g)).hom ≫ h' := by
  simp [transportBaseChange]

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
/-- The transported base change is again a base change of `h`. -/
theorem transportBaseChange_isPullback {T T' : Scheme.{u}} (g : T ⟶ W) (h : T' ⟶ T)
    (h' : pullback u (h ≫ g) ⟶ pullback u g)
    (sq : IsPullback (pullback.snd u (h ≫ g)) h' h (pullback.snd u g)) :
    IsPullback (pullback.snd v (h ≫ g)) (transportBaseChange v u θ hθ g h h') h
      (pullback.snd v g) := by
  refine sq.of_iso (transportPullbackIso v u θ hθ (h ≫ g)).symm (Iso.refl T')
    (transportPullbackIso v u θ hθ g).symm (Iso.refl T) ?_ ?_ ?_ ?_
  · simp
  · simp [transportBaseChange]
  · simp
  · simp

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] hv hu in
/-- The transported base change is a morphism over the base. -/
theorem transportBaseChange_comp_base {T T' : Scheme.{u}} (g : T ⟶ W) (h : T' ⟶ T)
    (h' : pullback u (h ≫ g) ⟶ pullback u g)
    (hfst : h' ≫ pullback.fst u g = pullback.fst u (h ≫ g)) :
    transportBaseChange v u θ hθ g h h' ≫ (pullback.fst v g ≫ sA) =
      pullback.fst v (h ≫ g) ≫ sA := by
  rw [reassoc_of% transportBaseChange_fst v u θ hθ g h h' hfst]

/-! ### The proper-pushforward axiom of a transport -/

omit [LocallyOfFiniteType u] in
/-- The cap operation of the transport of `c` along `θ` commutes with proper pushforward: the
proper-pushforward axiom of Stacks 0B76 for the transported class. -/
theorem bivariantTransportCap_proper_naturality (c : BivariantClass C G sA sW v hv p)
    {T T' : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback u (h ≫ g) ⟶ pullback u g)
    (sq : IsPullback (pullback.snd u (h ≫ g)) h' h (pullback.snd u g))
    (hfst : h' ≫ pullback.fst u g = pullback.fst u (h ≫ g)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sW) (g ≫ sW) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst u (h ≫ g) ≫ sB) (pullback.fst u g ≫ sB) h'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((h ≫ g) ≫ sW) k),
      bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k
          (properChowPushforward C ((h ≫ g) ≫ sW) (g ≫ sW) h (by simp [Category.assoc]) k
            hfac α) =
        properChowPushforward C (pullback.fst u (h ≫ g) ≫ sB) (pullback.fst u g ≫ sB) h'
          (by rw [← Category.assoc, hfst]) (k - p) hfac'
          (bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c (h ≫ g) k α) := by
  intro hfac hfac' α
  have hp' : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have hd := transportBaseChange_fst v u θ hθ g h h' hfst
  have sq' := transportBaseChange_isPullback v u θ hθ g h h' sq
  have hpd : IsProper (transportBaseChange v u θ hθ g h h') :=
    MorphismProperty.of_isPullback sq' (P := @IsProper) inferInstance
  have hdbase := transportBaseChange_comp_base C sA v u θ hθ g h h' hfst
  have hκbase := transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g
  have hκbase' := transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ (h ≫ g)
  have hh'base : h' ≫ (pullback.fst u g ≫ sB) = pullback.fst u (h ≫ g) ≫ sB := by
    rw [reassoc_of% hfst]
  have hfacd : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst v (h ≫ g) ≫ sA) (pullback.fst v g ≫ sA)
      (transportBaseChange v u θ hθ g h h') hdbase (k - p) :=
    properPushforwardFactorsThroughRationalEquivalence_isIso_comp_isIso C
      (pullback.fst v (h ≫ g) ≫ sA) (pullback.fst v g ≫ sA)
      (pullback.fst u (h ≫ g) ≫ sB) (pullback.fst u g ≫ sB)
      (transportPullbackIso v u θ hθ (h ≫ g)).hom h'
      (transportPullbackIso v u θ hθ g).inv hκbase' hh'base
      (by rw [Iso.inv_comp_eq, hκbase]) (k - p) hfac'
  rw [bivariantTransportCap_apply, bivariantTransportCap_apply,
    c.proper_naturality g h (transportBaseChange v u θ hθ g h h') sq' hd k hfac hfacd]
  exact properChowPushforward_comp_eq C (pullback.fst v (h ≫ g) ≫ sA) (pullback.fst v g ≫ sA)
    (pullback.fst u (h ≫ g) ≫ sB) (pullback.fst u g ≫ sB)
    (transportBaseChange v u θ hθ g h h') (transportPullbackIso v u θ hθ g).hom
    (transportPullbackIso v u θ hθ (h ≫ g)).hom h'
    (transportBaseChange_comp_hom v u θ hθ g h h') hdbase hκbase hκbase' hh'base (k - p) hfacd
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hκbase (k - p))
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hκbase' (k - p)) hfac'
    (c.cap (h ≫ g) k α)

/-! ### The flat-pullback axiom of a transport -/

omit [LocallyOfFiniteType u] in
/-- The cap operation of the transport of `c` along `θ` commutes with flat pullback of fixed
relative dimension: the flat axiom of Stacks 0B76 for the transported class.

The degrees are `(k + r) - p` on the left and `(k - p) + r` on the right, the same integer
written two ways, which is why the conclusion is an `HEq`. -/
theorem bivariantTransportCap_flat_naturality (c : BivariantClass C G sA sW v hv p)
    {T T' : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback u (h ≫ g) ⟶ pullback u g)
    (sq : IsPullback (pullback.snd u (h ≫ g)) h' h (pullback.snd u g))
    (hfst : h' ≫ pullback.fst u g = pullback.fst u (h ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sW) (g ≫ sW) h
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst u (h ≫ g) ≫ sB)
        (pullback.fst u g ≫ sB) h' (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (g ≫ sW) k),
      HEq
        (bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c (h ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ g) ≫ sW) (g ≫ sW) h (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst u (h ≫ g) ≫ sB) (pullback.fst u g ≫ sB) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
          (bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k α)) := by
  intro hr' hfac hfac' α
  have hft' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hfl' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hd := transportBaseChange_fst v u θ hθ g h h' hfst
  have sq' := transportBaseChange_isPullback v u θ hθ g h h' sq
  have hftd : LocallyOfFiniteType (transportBaseChange v u θ hθ g h h') :=
    MorphismProperty.of_isPullback sq' (P := @LocallyOfFiniteType) inferInstance
  have hfld : Flat (transportBaseChange v u θ hθ g h h') :=
    MorphismProperty.of_isPullback sq' (P := @Flat) inferInstance
  have hdr : AlgebraicGeometry.RelativeDimension (transportBaseChange v u θ hθ g h h') r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq' hr
  have hdbase := transportBaseChange_comp_base C sA v u θ hθ g h h' hfst
  have hκbase := transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g
  have hκbase' := transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ (h ≫ g)
  have hh'base : h' ≫ (pullback.fst u g ≫ sB) = pullback.fst u (h ≫ g) ≫ sB := by
    rw [reassoc_of% hfst]
  have hfacd : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst v (h ≫ g) ≫ sA)
      (pullback.fst v g ≫ sA) (transportBaseChange v u θ hθ g h h') hdbase r hdr (k - p) :=
    flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C (pullback.fst v g ≫ sA)
      (pullback.fst v (h ≫ g) ≫ sA) (pullback.fst u g ≫ sB) (pullback.fst u (h ≫ g) ≫ sB)
      (transportPullbackIso v u θ hθ g).hom hκbase
      (transportPullbackIso v u θ hθ (h ≫ g)).hom hκbase'
      (transportBaseChange v u θ hθ g h h') hdbase h' hh'base
      (transportBaseChange_comp_hom v u θ hθ g h h') r hdr hr' (k - p) hfac'
  have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
  have hc := c.flat_naturality g h r hr (transportBaseChange v u θ hθ g h h') sq' hd k hdr
    hfac hfacd α
  rw [bivariantTransportCap_apply, bivariantTransportCap_apply,
    flatPullbackChow_chowPushforwardOfIso C (pullback.fst v g ≫ sA)
      (pullback.fst v (h ≫ g) ≫ sA) (pullback.fst u g ≫ sB) (pullback.fst u (h ≫ g) ≫ sB)
      (transportPullbackIso v u θ hθ g).hom hκbase
      (transportPullbackIso v u θ hθ (h ≫ g)).hom hκbase'
      (transportBaseChange v u θ hθ g h h') hdbase h' hh'base
      (transportBaseChange_comp_hom v u θ hθ g h h') r hdr hr' (k - p) hfacd hfac']
  exact heq_map_index hidx hc fun n x =>
    chowPushforwardOfIso C (pullback.fst v (h ≫ g) ≫ sA) (pullback.fst u (h ≫ g) ≫ sB)
      (transportPullbackIso v u θ hθ (h ≫ g)).hom hκbase' n x

/-! ### The Gysin axiom of a transport -/

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
/-- The induced isomorphisms of base changes commute with the base-change maps of a morphism of
test schemes. -/
@[reassoc]
theorem transportPullbackIso_hom_comp_bivariantBaseChangeMap {T T' : Scheme.{u}} (g : T ⟶ W)
    (h : T' ⟶ T) :
    (transportPullbackIso v u θ hθ (h ≫ g)).hom ≫ bivariantBaseChangeMap u g h =
      bivariantBaseChangeMap v g h ≫ (transportPullbackIso v u θ hθ g).hom := by
  refine pullback.hom_ext ?_ ?_ <;> simp [bivariantBaseChangeMap]

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] [LocallyOfFiniteType sW]
  [LocallyOfFiniteType v] [LocallyOfFiniteType u] in
include hv in
/-- The structure morphism of a base change of `v` over the base, read through its test
scheme. -/
theorem transport_snd_comp_structureMorphism_eq {T : Scheme.{u}} (g : T ⟶ W) :
    pullback.snd v g ≫ (g ≫ sW) = pullback.fst v g ≫ sA := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, hv]

/-- The cap operation of the transport of `c` along `θ` commutes with the Gysin map of the zero
scheme of a section of an invertible module on a test scheme: the Gysin axiom of Stacks 0B76 for
the transported class.

As for `Stacks.Chow.bivariantRestrictionCap_gysin_naturality`, this is not a consequence of the
axioms of `c`: the two cap operations land on isomorphic but different base changes, and the
first Chern class rules a `Stacks.Chow.GysinSystem` provides there are unrelated data. The
hypothesis is the isomorphism case of Stacks 02TA for the system. -/
theorem bivariantTransportCap_gysin_naturality (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback u g).sheaf.obj
      (pullback u g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd u g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd u g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd u g) L s
    let E := Stacks.Divisors.zeroScheme (pullback u g) L' s'
    ∀ (e : pullback u (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap u g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst u g ≫ sB) =
        pullback.fst u (D.subschemeι ≫ g) ≫ sB)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst u (D.subschemeι ≫ g) ≫ sB) (E.subschemeι ≫ pullback.fst u g ≫ sB)
        e.hom hbase (k - p))
      (α : chowGroup C (g ≫ sW) (k + 1)),
      properChowPushforward C (pullback.fst u (D.subschemeι ≫ g) ≫ sB)
          (E.subschemeι ≫ pullback.fst u g ≫ sB) e.hom hbase (k - p) hfac
          (bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c (D.subschemeι ≫ g) k
            (G.onChow (g ≫ sW) L s k α)) =
        G.onChow (pullback.fst u g ≫ sB) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst u g ≫ sB))
            (by omega : (k + 1) - p = (k - p) + 1))
            (bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g (k + 1) α)) := by
  dsimp only
  intro e he hbase hfac α
  have hidx : (k + 1) - p = (k - p) + 1 := by omega
  have hqo := transportPullbackIso_hom_snd v u θ hθ g
  have hκbase := transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g
  have hκbaseD := transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)
  have hjBase := comp_comp_of_comp (zeroSchemePullbackIso_hom_subschemeι (pullback.snd v g)
    (pullback.snd u g) (transportPullbackIso v u θ hθ g).hom hqo L s) hκbase
  have heOld : (((transportPullbackIso v u θ hθ
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).trans e).trans
          (zeroSchemePullbackIso (pullback.snd v g) (pullback.snd u g)
            (transportPullbackIso v u θ hθ g).hom hqo L s).symm).hom ≫
        (Stacks.Divisors.zeroScheme _ _ _).subschemeι =
      bivariantBaseChangeMap v g (Stacks.Divisors.zeroScheme T L s).subschemeι := by
    have hjjinv := zeroSchemePullbackIso_inv_subschemeι (pullback.snd v g) (pullback.snd u g)
      (transportPullbackIso v u θ hθ g).hom hqo L s
    rw [show inv (transportPullbackIso v u θ hθ g).hom =
      (transportPullbackIso v u θ hθ g).inv from by simp] at hjjinv
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hjjinv, reassoc_of% he, transportPullbackIso_hom_comp_bivariantBaseChangeMap_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hbaseOld := comp_comp_of_eq heOld
    (by simp [bivariantBaseChangeMap] :
      bivariantBaseChangeMap v g (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
        (pullback.fst v g ≫ sA) =
        pullback.fst v ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sA)
  have hfacOld := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hbaseOld
    (k - p)
  have hfacJ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hjBase (k - p)
  have hfacb := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hκbase
    ((k + 1) - p)
  have hfacb' := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hκbase
    ((k - p) + 1)
  have hfacD := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hκbaseD
    (k - p)
  have hc := c.gysin_naturality g L s k
    (((transportPullbackIso v u θ hθ
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).trans e).trans
        (zeroSchemePullbackIso (pullback.snd v g) (pullback.snd u g)
          (transportPullbackIso v u θ hθ g).hom hqo L s).symm) heOld hbaseOld hfacOld α
  have hgysApplied := GysinSystem.onChow_baseChangeIso hgys (g ≫ sW) (pullback.snd v g)
    (pullback.snd u g) (pullback.fst v g ≫ sA) (pullback.fst u g ≫ sB)
    (transport_snd_comp_structureMorphism_eq C sA sW v hv g)
    (transport_snd_comp_structureMorphism_eq C sB sW u hu g)
    (transportPullbackIso v u θ hθ g).hom hqo hκbase L s (k - p)
    (zeroSchemePullbackIso (pullback.snd v g) (pullback.snd u g)
      (transportPullbackIso v u θ hθ g).hom hqo L s).hom
    (zeroSchemePullbackIso_hom_subschemeι (pullback.snd v g) (pullback.snd u g)
      (transportPullbackIso v u θ hθ g).hom hqo L s) hjBase hfacJ hfacb'
    (Eq.mp (congrArg (chowGroup C (pullback.fst v g ≫ sA)) hidx) (c.cap g (k + 1) α))
  have hcap : ∀ {T' : Scheme.{u}} (g' : T' ⟶ W) [LocallyOfFiniteType g'] (k' : ℤ)
      (β : chowGroup C (g' ≫ sW) k')
      (hb : (transportPullbackIso v u θ hθ g').hom ≫ (pullback.fst u g' ≫ sB) =
        pullback.fst v g' ≫ sA)
      (hf : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst v g' ≫ sA)
        (pullback.fst u g' ≫ sB) (transportPullbackIso v u θ hθ g').hom hb (k' - p)),
      bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g' k' β =
        properChowPushforward C (pullback.fst v g' ≫ sA) (pullback.fst u g' ≫ sB)
          (transportPullbackIso v u θ hθ g').hom hb (k' - p) hf (c.cap g' k' β) :=
    fun g' _ k' β hb hf =>
      (bivariantTransportCap_apply C G sA sB sW v hv u hu θ hθ p c g' k' β).trans
        (DFunLike.congr_fun
          (properChowPushforward_eq_chowPushforwardOfIso C _ _ _ hb (k' - p) hf).symm _)
  have hcapD := hcap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
    (G.onChow (g ≫ sW) L s k α) hκbaseD hfacD
  have hcapg := hcap g (k + 1) α hκbase hfacb
  exact gysinNaturalityAssemble C hκbaseD hbase hbaseOld hjBase hκbase
    (by simp) hidx hfacD hfac hfacOld hfacJ hfacb hfacb' hcapD hcapg hc hgysApplied

/-! ### The transported class -/

/-- The transport of a bivariant class `c` of degree `p` for `v : A ⟶ W` along an isomorphism
`θ : A ≅ B` over `W`: the bivariant class of degree `p` for `u : B ⟶ W` whose cap operations are
those of `c`, read through the induced isomorphisms of the base changes.

The Gysin axiom of a transported class is not a consequence of the axioms of `c`, so the
construction carries the isomorphism case of Stacks 02TA for the Gysin system, exactly as
`Stacks.Chow.bivariantRestriction` does. -/
def bivariantTransport (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) : BivariantClass C G sB sW u hu p where
  cap g _ k := bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k
  cap_properPushforward := by
    intro T₀ T₀' g₀ _ w₀ _ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantTransportCap_proper_naturality C G sA sB sW v hv u hu θ hθ p c)
      g₀ w₀ w₀' sq₀ hfst₀ k₀ _ _ α₀
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantTransportCap_flat_naturality C G sA sB sW v hv u hu θ hθ p c)
      g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact (bivariantTransportCap_gysin_naturality C G sA sB sW v hv u hu θ hθ p hgys c)
      g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-- The transported class caps by the transported cap operation. -/
@[simp]
theorem bivariantTransport_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sW) k) :
    (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c).cap g k α =
      bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k α :=
  rfl

/-- The assertion that a bivariant class for `u : B ⟶ W` is the transport of `c` along
`θ : A ≅ B`: on every test scheme its cap operation is that of `c`, read through the induced
isomorphism of the base changes. -/
def IsBivariantTransport (c : BivariantClass C G sA sW v hv p)
    (c' : BivariantClass C G sB sW u hu p) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sW) k),
    c'.cap g k α = bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k α

/-- The cap formula determines the transport: two bivariant classes that are both the transport
of `c` along `θ` are equal. -/
theorem eq_of_isBivariantTransport {c : BivariantClass C G sA sW v hv p}
    {c' d' : BivariantClass C G sB sW u hu p}
    (hc' : IsBivariantTransport C G sA sB sW v hv u hu θ hθ p c c')
    (hd' : IsBivariantTransport C G sA sB sW v hv u hu θ hθ p c d') : c' = d' := by
  refine BivariantClass.ext C G sB sW u hu p ?_
  intro T g _ k α
  rw [hc' g k α, hd' g k α]

/-- The transport of `c` along `θ` is the transport of `c` along `θ`: the construction satisfies
the characterization, so it is the unique class that does. -/
theorem isBivariantTransport_bivariantTransport (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) :
    IsBivariantTransport C G sA sB sW v hv u hu θ hθ p c
      (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c) := by
  intro T g _ k α
  rfl

namespace IsBivariantTransport

/-- Transport is additive: the transport of a sum is the sum of the transports. -/
theorem add {c d : BivariantClass C G sA sW v hv p} {c' d' : BivariantClass C G sB sW u hu p}
    (hc : IsBivariantTransport C G sA sB sW v hv u hu θ hθ p c c')
    (hd : IsBivariantTransport C G sA sB sW v hv u hu θ hθ p d d') :
    IsBivariantTransport C G sA sB sW v hv u hu θ hθ p (c + d) (c' + d') := by
  intro T g _ k α
  rw [BivariantClass.add_cap, hc g k α, hd g k α]
  simp only [bivariantTransportCap_apply, BivariantClass.add_cap, map_add]

/-- Transport negates: the transport of a negated class is the negated transport. -/
theorem neg {c : BivariantClass C G sA sW v hv p} {c' : BivariantClass C G sB sW u hu p}
    (hc : IsBivariantTransport C G sA sB sW v hv u hu θ hθ p c c') :
    IsBivariantTransport C G sA sB sW v hv u hu θ hθ p (-c) (-c') := by
  intro T g _ k α
  rw [BivariantClass.neg_cap, hc g k α]
  simp only [bivariantTransportCap_apply, BivariantClass.neg_cap, map_neg]

/-- The transport of the zero class is zero. -/
theorem zero : IsBivariantTransport C G sA sB sW v hv u hu θ hθ p 0 0 := by
  intro T g _ k α
  rw [BivariantClass.zero_cap]
  simp only [bivariantTransportCap_apply, BivariantClass.zero_cap, map_zero]

end IsBivariantTransport

/-- Transport along `θ` is additive. -/
theorem bivariantTransport_add (hgys : G.IsNaturalUnderBaseChangeIso)
    (c d : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys (c + d) =
      bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c +
        bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys d :=
  eq_of_isBivariantTransport C G sA sB sW v hv u hu θ hθ p
    (isBivariantTransport_bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys (c + d))
    (IsBivariantTransport.add C G sA sB sW v hv u hu θ hθ p
      (isBivariantTransport_bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c)
      (isBivariantTransport_bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys d))

/-- Transport along `θ` commutes with negation. -/
theorem bivariantTransport_neg (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys (-c) =
      -bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c :=
  eq_of_isBivariantTransport C G sA sB sW v hv u hu θ hθ p
    (isBivariantTransport_bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys (-c))
    (IsBivariantTransport.neg C G sA sB sW v hv u hu θ hθ p
      (isBivariantTransport_bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c))

/-- Transport along `θ` carries the zero class to the zero class. -/
theorem bivariantTransport_zero (hgys : G.IsNaturalUnderBaseChangeIso) :
    bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys 0 = 0 :=
  eq_of_isBivariantTransport C G sA sB sW v hv u hu θ hθ p
    (isBivariantTransport_bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys 0)
    (IsBivariantTransport.zero C G sA sB sW v hv u hu θ hθ p)

/-- Transport along an isomorphism over `W`, as a homomorphism of groups
`A^p(A ⟶ W) ⟶ A^p(B ⟶ W)`. -/
def bivariantTransportAddHom (hgys : G.IsNaturalUnderBaseChangeIso) :
    BivariantClass C G sA sW v hv p →+ BivariantClass C G sB sW u hu p where
  toFun c := bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c
  map_zero' := bivariantTransport_zero C G sA sB sW v hv u hu θ hθ p hgys
  map_add' := bivariantTransport_add C G sA sB sW v hv u hu θ hθ p hgys

end Transport

end Stacks.Chow

end
