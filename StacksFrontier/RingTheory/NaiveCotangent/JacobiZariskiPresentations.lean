module

public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiSixTerm
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# The Jacobi-Zariski six-term exact sequence over arbitrary presentations

`NaiveCotangent.jacobiZariski_sixTerm_exact` is **Stacks 00S2** for the three presentations the
source's own proof uses: a presentation `α : A[x_s] → B` of `B` over `A`, a presentation
`β : B[y_t] → C` of `C` over `B`, and the presentation `γ : A[x_s, y_t] → C` of `C` over `A`
that those two induce.  The middle column of the diagram is therefore pinned to `Q.comp P`,
which is not the presentation a consumer has: the canonical presentation `A[C] → C` of Stacks
07BL, in particular, is not of that form, and it is the canonical presentation that the stalk of
the naive cotangent complex is computed in (Stacks 0D09).

This file moves the sequence off `Q.comp P`.  Let `N` be *any* presentation of `C` over `A`.
Stacks 00S1 (4) (`NaiveCotangent.nlMap_isHomotopyEquiv_and_isQuasiIso`, at `R = R'` and
`S = S'`, where the two structure maps are the identity of `A` and of `C` and so bijective) says
that a morphism of presentations `γ ⟶ N` induces a quasi-isomorphism `NL(γ) ⟶ NL(N)`, and Stacks
00S1 (2) and (3) say that the two comparison chain maps of the sequence are carried onto the
comparison chain maps attached to `N` by that quasi-isomorphism.  Exactness transports, so the
six-term sequence holds over `α`, `N` and `β`, with its three terms the naive cotangent
complexes of three presentations chosen independently of one another.  Taking all three
canonical gives the sequence between `NL_{B/A} ⊗_B C`, `NL_{C/A}` and `NL_{C/B}`, which is the
form the stalkwise statements of Stacks 0E1Y need.

The connecting map is unchanged: its source `H₁(NL(β))` and its target `H₀(NL(α) ⊗_B C)` are
terms of the sequence that do not involve the middle presentation, so
`NaiveCotangent.jacobiZariskiConnecting` already is the connecting map of the transported
sequence.

## Main results

* `NaiveCotangent.homotopic_nlExtensionOverMap`: two morphisms of extensions of one and the same
  algebra induce homotopic chain maps, so `NaiveCotangent.onH₁_nlExtensionOverMap_eq` and
  `NaiveCotangent.onH₀_nlExtensionOverMap_eq`: the maps they induce on homology do not depend on
  the morphism.  This is Stacks 00S1 (2) for `NaiveCotangent.nlExtensionOverMap`, the companion
  of `NaiveCotangent.homotopic_nlExtensionBaseChangeMap`.
* `NaiveCotangent.nlExtensionOverMap_comp` and
  `NaiveCotangent.nlExtensionOverMap_comp_nlExtensionBaseChangeMap`: Stacks 00S1 (3) for those
  two comparison maps.
* `NaiveCotangent.jacobiZariski_sixTerm_exact_extension`: **Stacks 00S2 over three
  independently chosen presentations.**
* `NaiveCotangent.jacobiZariski_sixTerm_exact_canonical`: the same over the canonical
  presentations of Stacks 07BL, which is the form in which the stalk of Stacks 0E1Y is computed.

## Implementation notes

The two comparison maps are `NaiveCotangent.nlExtensionBaseChangeMap` and
`NaiveCotangent.nlExtensionOverMap` of
`StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget`, which are also the maps the
stalk of the canonical map of Stacks 0E1Y is identified with
(`Stacks.NaiveCotangentStalkBaseChange.stalkLegZeroLinear_baseChangeNaiveCotangentMap`), so the
sequence below is stated in the vocabulary its consumer uses.  They are stated for arbitrary
`Algebra.Extension.Hom`s rather than for `Algebra.Generators.Hom`s, which is both more general
and what that identification produces; `NaiveCotangent.nlToComp` and
`NaiveCotangent.nlOfComp` are the two of them at `Algebra.Generators.toComp` and
`Algebra.Generators.ofComp` (`NaiveCotangent.nlToComp_eq`, `NaiveCotangent.nlOfComp_eq`).

`NaiveCotangent.nlExtensionOverMap_comp_nlExtensionBaseChangeMap` and
`NaiveCotangent.nlExtensionBaseChangeMap_comp_eq` are two instances of one statement — the
functoriality of the base-changed comparison in a morphism of extensions of the target — the
first for arbitrary extensions over one base, the second for the canonical presentations over
two bases.  Both are special cases of the same identity over three bases, which should replace
the pair.

Exactness is transported by three elementary lemmas about linear maps,
`NaiveCotangent.exact_of_bijective_middle`,
`NaiveCotangent.exact_of_exact_of_surjective_comp` and
`NaiveCotangent.exact_of_injective_comp`, rather than by rewriting along an isomorphism: the
quasi-isomorphism of Stacks 00S1 (4) is a bijection of homology modules, not an isomorphism of
complexes, and the two comparison maps are identified with its composites only up to homotopy.

`NaiveCotangent.nlRestrict T N` and `NaiveCotangent.NL N` agree for a presentation `N` of a
`T`-algebra over which no scalars are restricted, so the statements of Stacks 00S1, which are
about `NaiveCotangent.nlMap`, apply to `NaiveCotangent.nlExtensionOverMap` as they stand; the
two spellings are definitionally equal but not syntactically so, which is why the proof below
composes equalities with `Eq.trans` and `DFunLike.congr_fun` instead of rewriting.

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), Lemma 10.134.4.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), Lemma 10.134.2.
* [Stacks Project, Tag 07BL](https://stacks.math.columbia.edu/tag/07BL), the canonical
  presentation.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the consumer: the
  stalkwise form of the six-term sequence of a tower of sheaves of rings.
-/

@[expose] public section

universe w₁ w₂ w₃ u₁ u₂ u₃

open Algebra Function TensorProduct

namespace NaiveCotangent

/-! ### Transporting exactness along maps of the terms -/

section Transport

variable {S : Type*} [CommRing S]
variable {A B B' C C' : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup B'] [AddCommGroup C] [AddCommGroup C']
  [Module S A] [Module S B] [Module S B'] [Module S C] [Module S C']

/-- **Exactness transports along a bijection of the middle term.**  If `e : B → B'` is bijective
and carries `f : A → B` to `f' : A → B'` and `g' : B' → C` back to `g : B → C`, then `f'` and
`g'` are exact as soon as `f` and `g` are. -/
theorem exact_of_bijective_middle {f : A →ₗ[S] B} {g : B →ₗ[S] C} {e : B →ₗ[S] B'}
    {f' : A →ₗ[S] B'} {g' : B' →ₗ[S] C} (he : Bijective e) (hf : ∀ a, e (f a) = f' a)
    (hg : ∀ y, g' (e y) = g y) (h : Exact f g) : Exact f' g' := fun z ↦ by
  obtain ⟨y, rfl⟩ := he.surjective z
  rw [hg y]
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · obtain ⟨a, ha⟩ := (h y).1 hy
    exact ⟨a, by rw [← hf a, ha]⟩
  · obtain ⟨a, ha⟩ := hy
    refine (h y).2 ⟨a, he.injective ?_⟩
    rw [hf a, ha]

/-- Precomposing the first map of an exact pair with a surjection does not change exactness. -/
theorem exact_of_exact_of_surjective_comp {f : A →ₗ[S] B} {g : B →ₗ[S] C} {A' : Type*}
    [AddCommGroup A'] [Module S A'] {s : A' →ₗ[S] A} {fs : A' →ₗ[S] B} (hs : Surjective s)
    (hfs : ∀ a', fs a' = f (s a')) (h : Exact fs g) : Exact f g := fun y ↦ by
  rw [h y]
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · obtain ⟨a', ha⟩ := hy
    exact ⟨s a', by rw [← hfs a', ha]⟩
  · obtain ⟨a, ha⟩ := hy
    obtain ⟨a', rfl⟩ := hs a
    exact ⟨a', by rw [hfs a', ha]⟩

/-- Postcomposing the second map of an exact pair with an injection does not change
exactness. -/
theorem exact_of_injective_comp {f : A →ₗ[S] B} {g : B →ₗ[S] C} {i : C →ₗ[S] C'}
    {g' : B →ₗ[S] C'} (hi : Injective i) (hg : ∀ y, g' y = i (g y)) (h : Exact f g) :
    Exact f g' := fun y ↦ by
  rw [hg y, ← h y]
  exact ⟨fun hy ↦ hi (by rw [hy, map_zero]), fun hy ↦ by rw [hy, map_zero]⟩

end Transport

/-! ### Stacks 00S1 (2) and (3) for the comparison of two extensions of one algebra -/

section OverMap

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' T] [IsScalarTower R R' T]
variable {P : Extension R T} {Q : Extension R' T}

/-- **Stacks 00S1 (2) for `NaiveCotangent.nlExtensionOverMap`.**  Any two morphisms of
extensions `α → β` of one and the same algebra `C`, over two bases `A → A'`, induce homotopic
chain maps `NL(α) ⟶ NL(β)`; the homotopy is `Algebra.Extension.Hom.sub`.  This is the companion
of `NaiveCotangent.homotopic_nlExtensionBaseChangeMap`. -/
theorem homotopic_nlExtensionOverMap (h h' : P.Hom Q) :
    Homotopic (nlExtensionOverMap h) (nlExtensionOverMap h') :=
  ⟨h.sub h', Extension.Cotangent.map_sub_map h h',
    Extension.CotangentSpace.map_sub_map h h'⟩

/-- The map induced on `H₁` does not depend on the morphism of extensions. -/
theorem onH₁_nlExtensionOverMap_eq (h h' : P.Hom Q) :
    (nlExtensionOverMap h).onH₁ = (nlExtensionOverMap h').onH₁ :=
  ChainMap.onH₁_eq_of_homotopic (homotopic_nlExtensionOverMap h h')

/-- The map induced on `H₀` does not depend on the morphism of extensions. -/
theorem onH₀_nlExtensionOverMap_eq (h h' : P.Hom Q) :
    (nlExtensionOverMap h).onH₀ = (nlExtensionOverMap h').onH₀ :=
  ChainMap.onH₀_eq_of_homotopic (homotopic_nlExtensionOverMap h h')

/-- **Stacks 00S1 (3) for `NaiveCotangent.nlExtensionOverMap`.**  The chain map of a composite
of morphisms of extensions of one algebra is the composite of the two chain maps. -/
theorem nlExtensionOverMap_comp {P₀ : Extension R T} (h : P₀.Hom P) (h' : P.Hom Q) :
    (nlExtensionOverMap h').comp (nlExtensionOverMap h) = nlExtensionOverMap (h'.comp h) :=
  ChainMap.ext (Extension.Cotangent.map_comp _ h h').symm
    (Extension.CotangentSpace.map_comp h h').symm

end OverMap

/-! ### Stacks 00S1 (3) for the base-changed comparison -/

section BaseChangeComp

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
variable {P : Extension R S} {Q Q' : Extension R T}

omit [IsScalarTower R S T] in
/-- The degree-`1` half of
`NaiveCotangent.nlExtensionOverMap_comp_nlExtensionBaseChangeMap`. -/
theorem liftBaseChange_cotangentMap_comp (h : P.Hom Q) (h' : Q.Hom Q') :
    Extension.Cotangent.map h' ∘ₗ (Extension.Cotangent.map h).liftBaseChange T =
      (Extension.Cotangent.map (h'.comp h)).liftBaseChange T := by
  rw [LinearMap.liftBaseChange_comp, Extension.Cotangent.map_comp]

omit [IsScalarTower R S T] in
/-- The degree-`0` half of
`NaiveCotangent.nlExtensionOverMap_comp_nlExtensionBaseChangeMap`. -/
theorem liftBaseChange_cotangentSpaceMap_comp (h : P.Hom Q) (h' : Q.Hom Q') :
    Extension.CotangentSpace.map h' ∘ₗ (Extension.CotangentSpace.map h).liftBaseChange T =
      (Extension.CotangentSpace.map (h'.comp h)).liftBaseChange T := by
  rw [LinearMap.liftBaseChange_comp, Extension.CotangentSpace.map_comp]

omit [IsScalarTower R S T] in
/-- **Stacks 00S1 (3) for the base-changed comparison.**  The base-changed comparison
`NL(α) ⊗_B C ⟶ NL(β)` attached to a morphism of extensions `α → β`, followed by the chain map of
a morphism `β → β'` of extensions of `C` over the same base, is the base-changed comparison of
the composite.

This is `NaiveCotangent.nlExtensionBaseChangeMap_comp_eq` for arbitrary extensions over one base
instead of the canonical presentations over two bases; both are special cases of the same
identity over three bases. -/
theorem nlExtensionOverMap_comp_nlExtensionBaseChangeMap (h : P.Hom Q) (h' : Q.Hom Q') :
    (nlExtensionOverMap h').comp (nlExtensionBaseChangeMap (T := T) h) =
      nlExtensionBaseChangeMap (T := T) (h'.comp h) :=
  ChainMap.ext (liftBaseChange_cotangentMap_comp h h')
    (liftBaseChange_cotangentSpaceMap_comp h h')

end BaseChangeComp

/-! ### The two comparison maps of the source's own proof -/

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w₁} {σ : Type w₂} {τ : Type w₃}

/-- The comparison `NL(α) ⊗_B C ⟶ NL(γ)` of the source's own proof is the base-changed
comparison of the morphism of extensions underlying `Algebra.Generators.toComp`. -/
theorem nlToComp_eq (Q : Generators S T ι) (P : Generators R S σ) :
    nlToComp Q P = nlExtensionBaseChangeMap (T := T) (Q.toComp P).toExtensionHom := rfl

/-- The comparison `NL(γ) ⟶ NL(β)` of the source's own proof is the chain map of the morphism of
extensions underlying `Algebra.Generators.ofComp`. -/
theorem nlOfComp_eq (Q : Generators S T ι) (P : Generators R S σ) :
    nlOfComp Q P = nlExtensionOverMap (Q.ofComp P).toExtensionHom := rfl

/-! ### The six-term sequence over three independently chosen presentations -/

/-- Composing with a chain map and then passing to homology depends only on the homotopy class of
the composite. -/
private theorem onH_comp_apply_eq_of_homotopic {R₀ : Type*} [CommRing R₀] {X Y Z : TwoTerm R₀}
    {f : ChainMap X Y} {g : ChainMap Y Z} {k k' : ChainMap X Z} (hk : g.comp f = k)
    (hh : Homotopic k k') :
    (∀ a, g.onH₁ (f.onH₁ a) = k'.onH₁ a) ∧ (∀ a, g.onH₀ (f.onH₀ a) = k'.onH₀ a) := by
  subst hk
  exact ⟨fun a ↦ by rw [← LinearMap.comp_apply, ← ChainMap.onH₁_comp,
      ChainMap.onH₁_eq_of_homotopic hh],
    fun a ↦ by rw [← LinearMap.comp_apply, ← ChainMap.onH₀_comp,
      ChainMap.onH₀_eq_of_homotopic hh]⟩

/-- **The Jacobi-Zariski six-term exact sequence over three independently chosen
presentations** (Stacks 00S2 together with Stacks 00S1).  Let `A → B → C` be ring maps, let
`α : A[x_s] → B` be a presentation of `B` over `A`, let `β : B[y_t] → C` be a presentation of
`C` over `B` and let `N` be *any* presentation of `C` over `A`.  Choose morphisms of extensions
`varphi : α ⟶ N` over the square with vertical morphisms `id_A` and `B → C`, and
`psi : N ⟶ β` over the square with vertical morphisms `A → B` and `id_C`.  Then
```
H₁(NL(α) ⊗_B C) → H₁(NL(N)) → H₁(NL(β)) --δ--> H₀(NL(α) ⊗_B C) → H₀(NL(N)) → H₀(NL(β)) → 0
```
is exact at each of its five interior nodes, `δ` being
`NaiveCotangent.jacobiZariskiConnecting`.

The two comparison maps do not depend on the choice of `varphi` and `psi`
(`NaiveCotangent.homotopic_nlExtensionBaseChangeMap` and
`NaiveCotangent.homotopic_nlExtensionOverMap`, which are Stacks 00S1 (2)), so the sequence is
canonical. -/
@[stacks 00S2 "the six-term exact sequence with its middle column an ARBITRARY presentation of \
`C` over `A`, rather than the presentation `Q.comp P` induced by the other two, which is what \
`NaiveCotangent.jacobiZariski_sixTerm_exact` gives; the two are compared by Stacks 00S1 (4), \
which this statement uses but does not state"]
theorem jacobiZariski_sixTerm_exact_extension (Q : Generators S T ι)
    (P : Generators R S σ) (N : Generators R T τ)
    (φ : P.toExtension.Hom N.toExtension) (ψ : N.toExtension.Hom Q.toExtension) :
    Exact (nlExtensionBaseChangeMap (T := T) φ).onH₁ (nlExtensionOverMap ψ).onH₁ ∧
      Exact (nlExtensionOverMap ψ).onH₁ (jacobiZariskiConnecting Q P) ∧
      Exact (jacobiZariskiConnecting Q P) (nlExtensionBaseChangeMap (T := T) φ).onH₀ ∧
      Exact (nlExtensionBaseChangeMap (T := T) φ).onH₀ (nlExtensionOverMap ψ).onH₀ ∧
      Surjective (nlExtensionOverMap ψ).onH₀ := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := jacobiZariski_sixTerm_exact Q P
  obtain ⟨g⟩ : Nonempty ((Q.comp P).Hom N) := ⟨Generators.defaultHom (Q.comp P) N⟩
  -- Stacks 00S1 (4): the comparison of `NL(γ)` with `NL(N)` is a quasi-isomorphism.
  obtain ⟨hu₁, hu₀⟩ : IsQuasiIso (nlExtensionOverMap g.toExtensionHom) :=
    (nlMap_isHomotopyEquiv_and_isQuasiIso (R' := R) (S' := T)
      (by rw [Algebra.algebraMap_self]; exact Function.bijective_id)
      (by rw [Algebra.algebraMap_self]; exact Function.bijective_id)
      (Q.comp P) N g).right
  -- Stacks 00S1 (3) and (2): `NL(α) ⊗ C ⟶ NL(γ)` followed by it is `NL(α) ⊗ C ⟶ NL(N)`.
  obtain ⟨key₁, key₀⟩ := onH_comp_apply_eq_of_homotopic
    (nlExtensionOverMap_comp_nlExtensionBaseChangeMap (T := T) (Q.toComp P).toExtensionHom
      g.toExtensionHom) (homotopic_nlExtensionBaseChangeMap (T := T) _ φ)
  obtain ⟨rel₁, rel₀⟩ := onH_comp_apply_eq_of_homotopic
    (nlExtensionOverMap_comp g.toExtensionHom ψ)
    (homotopic_nlExtensionOverMap (ψ.comp g.toExtensionHom) (Q.ofComp P).toExtensionHom)
  refine ⟨exact_of_bijective_middle hu₁ key₁ rel₁ e₁,
    exact_of_exact_of_surjective_comp hu₁.surjective (fun z ↦ (rel₁ z).symm) e₂,
    exact_of_injective_comp hu₀.injective (fun z ↦ (key₀ z).symm) e₃,
    exact_of_bijective_middle hu₀ key₀ rel₀ e₄, ?_⟩
  have hs : Surjective ((nlExtensionOverMap ψ).onH₀ ∘
      (nlExtensionOverMap g.toExtensionHom).onH₀) := fun y ↦ by
    obtain ⟨z, hz⟩ := e₅ y
    exact ⟨z, (rel₀ z).trans hz⟩
  exact hs.of_comp

/-! ### The six-term sequence over the canonical presentations -/

/-- **The Jacobi-Zariski six-term exact sequence over the canonical presentations** of Stacks
07BL.  For ring maps `A → B → C`,
```
H₁(NL_{B/A} ⊗_B C) → H₁(NL_{C/A}) → H₁(NL_{C/B}) --δ--> C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B} → 0
```
is exact at each of its five interior nodes, the three complexes being the naive cotangent
complexes of the canonical presentations `A[B] → B`, `A[C] → C` and `B[C] → C`, and the two
comparison maps those attached to any morphisms of extensions between them, on which they do
not depend.

This is `NaiveCotangent.jacobiZariski_sixTerm_exact_extension` at the canonical presentation of
`C` over `A`; it is the form in which the stalkwise statements of Stacks 0E1Y need it, the stalk
of the naive cotangent complex being the naive cotangent complex of the canonical presentation
of the stalk (Stacks 0D09), and the stalk of the canonical map `c₁` of Stacks 0E1Y being
`NaiveCotangent.nlExtensionBaseChangeMap` of a morphism of those canonical presentations
(`Stacks.NaiveCotangentStalkBaseChange.stalkLegZeroLinear_baseChangeNaiveCotangentMap`). -/
@[stacks 00S2 "the six-term exact sequence between the naive cotangent complexes of the three \
CANONICAL presentations of Stacks 07BL, rather than of the three presentations of the source's \
own proof"]
theorem jacobiZariski_sixTerm_exact_canonical
    (φ : (canonicalGenerators R S).toExtension.Hom (canonicalGenerators R T).toExtension)
    (ψ : (canonicalGenerators R T).toExtension.Hom (canonicalGenerators S T).toExtension) :
    Exact (nlExtensionBaseChangeMap (T := T) φ).onH₁ (nlExtensionOverMap ψ).onH₁ ∧
      Exact (nlExtensionOverMap ψ).onH₁
        (jacobiZariskiConnecting (canonicalGenerators S T) (canonicalGenerators R S)) ∧
      Exact (jacobiZariskiConnecting (canonicalGenerators S T) (canonicalGenerators R S))
        (nlExtensionBaseChangeMap (T := T) φ).onH₀ ∧
      Exact (nlExtensionBaseChangeMap (T := T) φ).onH₀ (nlExtensionOverMap ψ).onH₀ ∧
      Surjective (nlExtensionOverMap ψ).onH₀ :=
  jacobiZariski_sixTerm_exact_extension (canonicalGenerators S T) (canonicalGenerators R S)
    (canonicalGenerators R T) φ ψ

/-! ### The two middle exactness assertions, elementwise

`NaiveCotangent.H₁` is a submodule and `NaiveCotangent.H₀` a quotient module, so an exactness
assertion about them is an assertion about kernels and cokernels of the differentials.  The two
readings below are the shape in which a statement about complexes of modules consumes it:
`HomologicalComplex.exact_homologyMap_of_exists_cycle` and
`HomologicalComplex.exact_homologyMap_of_exists_add_d` of
`StacksFrontier.Algebra.Homology.TwoTermHomologyExact`.
-/

section Elementwise

variable {S : Type*} [CommRing S] {X Y Z : TwoTerm S}

/-- The degree-`1` term of a chain map, read on the submodule `NaiveCotangent.H₁`. -/
theorem onH₁_coe (f : ChainMap X Y) (x : H₁ X) : ((f.onH₁ x : H₁ Y) : Y.X₁) = f.f₁ (x : X.X₁) :=
  rfl

/-- The degree-`0` term of a chain map, read on the quotient module `NaiveCotangent.H₀`. -/
theorem onH₀_mkQ (f : ChainMap X Y) (n : X.X₀) :
    f.onH₀ ((LinearMap.range X.d).mkQ n) = (LinearMap.range Y.d).mkQ (f.f₀ n) :=
  rfl

/-- **Exactness at `H₁`, elementwise.**  A cycle of the middle complex killed by the second
chain map is the image of a cycle of the first. -/
theorem exists_cycle_of_exact_onH₁ (f : ChainMap X Y) (g : ChainMap Y Z)
    (h : Exact f.onH₁ g.onH₁) (y : Y.X₁) (hy : Y.d y = 0) (hgy : g.f₁ y = 0) :
    ∃ x : X.X₁, X.d x = 0 ∧ f.f₁ x = y := by
  have hmem : y ∈ H₁ Y := LinearMap.mem_ker.mpr hy
  obtain ⟨x, hx⟩ := (h ⟨y, hmem⟩).1 (Subtype.ext ((onH₁_coe g ⟨y, hmem⟩).trans hgy))
  exact ⟨(x : X.X₁), LinearMap.mem_ker.mp x.2,
    (onH₁_coe f x).symm.trans (congrArg Subtype.val hx)⟩

/-- **Exactness at `H₀`, elementwise.**  An element of the degree-`0` term of the middle complex
whose image under the second chain map is a boundary differs from an element of the image of the
first chain map by a boundary. -/
theorem exists_add_d_of_exact_onH₀ (f : ChainMap X Y) (g : ChainMap Y Z)
    (h : Exact f.onH₀ g.onH₀) (n : Y.X₀) (hn : ∃ m : Z.X₁, Z.d m = g.f₀ n) :
    ∃ (n' : X.X₀) (z : Y.X₁), f.f₀ n' + Y.d z = n := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨c, hc⟩ := (h ((LinearMap.range Y.d).mkQ n)).1
    ((onH₀_mkQ g n).trans ((Submodule.Quotient.mk_eq_zero _).2 ⟨m, hm⟩))
  obtain ⟨n', rfl⟩ := Submodule.mkQ_surjective (LinearMap.range X.d) c
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 ((onH₀_mkQ f n').symm.trans hc)
  refine ⟨n', -z, ?_⟩
  rw [map_neg, hz]
  abel

/-- **Surjectivity on `H₀`, elementwise.**  Every element of the degree-`0` term of the target
differs from an element of the image of the chain map by a boundary. -/
theorem exists_add_d_of_surjective_onH₀ (f : ChainMap X Y) (h : Surjective f.onH₀) (n : Y.X₀) :
    ∃ (m : X.X₀) (z : Y.X₁), f.f₀ m + Y.d z = n := by
  obtain ⟨c, hc⟩ := h ((LinearMap.range Y.d).mkQ n)
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range X.d) c
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 ((onH₀_mkQ f m).symm.trans hc)
  refine ⟨m, -z, ?_⟩
  rw [map_neg, hz]
  abel

end Elementwise

end NaiveCotangent

end
