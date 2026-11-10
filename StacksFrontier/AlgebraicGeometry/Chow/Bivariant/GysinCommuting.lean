module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality

/-!
# The bivariant Gysin class of a divisor commutes with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `(𝓛, s, i : D ⟶ X)` be a triple as in Definition 02T8:
`𝓛` an invertible module on `X`, `s` a global section of `𝓛` and `i` the closed immersion of its
zero scheme. Let `f : Z ⟶ X` be a morphism of schemes locally of finite type and let
`c ∈ A^p(Z ⟶ X)` be a bivariant class. Stacks 0FA3 asserts that the bivariant Gysin class
`c' ∈ A^1(D ⟶ X)` of Stacks 0B79 commutes with `c` in the sense of Stacks 0FA2, and that this is
a restatement of condition (3) of Definition 0B76 — the axiom saying that capping with `c`
commutes with the Gysin map of every pulled-back divisor.

That is how it is proved here. The cap operation of `c'` on a test scheme `g : T ⟶ X` is the
Gysin map of the pulled-back section `g^*s`, read on the base change `D ×_X T` of the divisor
through the identification of Stacks 0B6Y; so the two iterated cap operations
`c' ∩ (c ∩ -)` and `c ∩ (c' ∩ -)` of Stacks 0FA2 are the two sides of
`Stacks.Chow.BivariantClass.gysin_naturality` for `c` at the divisor pulled back to `T`.

## Main definitions

* `Stacks.Chow.gysinTripleInclusion`, `Stacks.Chow.gysinTripleModule`,
  `Stacks.Chow.gysinTripleSection`, `Stacks.Chow.gysinTripleDivisor` — the triple of
  Definition 02T8 and its base change along a test scheme.
* `Stacks.Chow.gysinDivisorBaseChangeIso` — **Stacks 0B6Y**, the identification of the base
  change `D ×_X T` with the zero scheme of the pulled-back section.
* `Stacks.Chow.gysinBivariantCap` — the cap operation of the bivariant Gysin class of
  Stacks 0B79.
* `Stacks.Chow.IsGysinBivariantClass` — **the characterization of Stacks 0B79**: that a bivariant
  class of degree one for `i : D ⟶ X` caps by that Gysin map on every test scheme.
* `Stacks.Chow.testBaseChangeIso` — the isomorphism of the two base changes of `f : X ⟶ Y`
  induced by an isomorphism of test schemes over `Y`.

## Main results

* `Stacks.Chow.gysinBivariantCommute` — **Stacks 0FA3**: a bivariant class `c'` for
  `i : D ⟶ X` of degree one satisfying the characterization of Stacks 0B79 commutes with every
  bivariant class `c ∈ A^p(Z ⟶ X)`, in the sense of `Stacks.Chow.BivariantCommute`.
* `Stacks.Chow.BivariantClass.gysin_naturality_baseChangeDivisor`,
  `Stacks.Chow.BivariantClass.gysin_naturality_gysinCap` — condition (3) of Stacks 0B76, read
  for the divisor pulled back to a test scheme and in the degrees the commutation of
  Stacks 0FA2 uses.
* `Stacks.Chow.BivariantClass.cap_chowPushforwardOfIso` — condition (1) of Stacks 0B76 for an
  isomorphism of test schemes.
* `Stacks.Chow.GysinSystem.onChow_pullbackComp` — the Gysin maps of the two readings of a section
  pulled back in two steps agree, for a morphism presented as a composite.

## Implementation notes

### Why `c'` is an argument

The class `c'` of Stacks 0B79 is `Stacks.Chow.gysinBivariantClass` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass`, which is built downstream of this
file:
its Gysin axiom needs the commutation of two Gysin maps, proved from the key formula of
Stacks 0AYC far downstream of the bivariant vocabulary. So Stacks 0FA3 is stated here for a
bivariant class `c'` capping by the Gysin map of the pulled-back section —
`Stacks.Chow.IsGysinBivariantClass`, which determines it uniquely by
`Stacks.Chow.BivariantClass.ext` and which the class of Stacks 0B79 satisfies. The commutation is
*derived* from `Stacks.Chow.BivariantClass.gysin_naturality`, condition (3) of Stacks 0B76 for
`c`; it is in no way assumed.

### The one carried hypothesis on the Gysin system

`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality` is carried. It is needed
because the Gysin axiom of `c` produces the Gysin map of `𝓛` pulled back to `T` and then to
`Z ×_X T`, while the cap operation of `c'` at the test scheme `Z ×_X T ⟶ X` is the Gysin map of
`𝓛` pulled back along the composite; the two zero schemes agree by
`Stacks.Divisors.zeroScheme_pullback_comp`, but a `Stacks.Chow.GysinSystem` assigns the two
invertible modules *a priori* unrelated first Chern class rules. As recorded there, this is a
property of the chosen datum and not a statement of the Stacks Project: it holds for the Gysin
map of Stacks 02TO, whose first Chern class rule depends on the invertible module only through
its isomorphism class.

### Where `@[stacks 0B79]` sits

`Stacks.Chow.gysinBivariantCap` and `Stacks.Chow.IsGysinBivariantClass` are the cap operation of
Stacks 0B79 and its characterization. The tag asserts that this operation is a bivariant class,
and it is registered on `Stacks.Chow.gysinBivariantClass`, where that is proved.

## References

* [Stacks Project, Tag 0FA3](https://stacks.math.columbia.edu/tag/0FA3)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- The zero scheme of a section pulled back in two steps is the zero scheme of the section
pulled back along a morphism equal to the composite. -/
theorem zeroScheme_pullback_comp_eq {A B T : Scheme.{u}} (q₁ : A ⟶ B) (q₂ : B ⟶ T) (q : A ⟶ T)
    (hq : q₁ ≫ q₂ = q) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    zeroScheme A ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) =
      zeroScheme A ((Scheme.Modules.pullback q).obj L)
        (AlgebraicGeometry.pullbackGlobalSections q L s) := by
  subst hq
  exact zeroScheme_pullback_comp q₁ q₂ L s

end Stacks.Divisors

namespace Stacks.Chow

/-! ### Transport bookkeeping -/

/-- The transport of a Chow group along an equality of degrees, written as a cast of types. -/
theorem eqMp_chowGroup (C : ChowSituation.{u}) {A : Scheme.{u}} (q : A ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (h : i = j) (x : chowGroup C q i) :
    Eq.mp (congrArg (chowGroup C q) h) x = chowGroupDegreeEquiv C q h x := by
  subst h
  rfl

/-- The Gysin map of a Gysin system commutes with the transport of a Chow group along an equality
of degrees. -/
theorem GysinSystem.onChow_chowGroupDegreeEquiv {C : ChowSituation.{u}} (G : GysinSystem C)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {k l : ℤ} (h : k = l) (h' : k + 1 = l + 1) (α : chowGroup C q (k + 1)) :
    chowGroupDegreeEquiv C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) h
        (G.onChow q L s k α) =
      G.onChow q L s l (chowGroupDegreeEquiv C q h' α) := by
  subst h
  rfl

section Transport

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p)

/-- The cap operation of a bivariant class, read in a fixed degree, does not depend on which of
two equal degrees the class is capped in. -/
theorem BivariantClass.cap_transport_eq {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    {k l j : ℤ} (hkl : k = l) (h₁ : k - p = j) (h₂ : l - p = j)
    (α : chowGroup C (g ≫ sY) k) :
    chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) h₁ (c.cap g k α) =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) h₂
        (c.cap g l (chowGroupDegreeEquiv C (g ≫ sY) hkl α)) := by
  subst hkl
  rfl

/-- The degree bookkeeping of condition (3) of Stacks 0B76: the class `c ∩ α` fed to the Gysin
map of the base change, read in the degree `(k - p) - 1` that the commutation of Stacks 0FA2
uses rather than in `((k - 1) - p) + 1`. -/
theorem BivariantClass.cap_gysin_degree_transport {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    chowGroupDegreeEquiv C (pullback.fst f g ≫ sX)
        (show k - 1 - p + 1 = k - p - 1 + 1 by ring)
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
            (show k - 1 + 1 - p = k - 1 - p + 1 by ring))
          (c.cap g (k - 1 + 1)
            (chowGroupDegreeEquiv C (g ≫ sY) (show k = k - 1 + 1 by ring) α))) =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX)
        (show k - p = k - p - 1 + 1 by ring) (c.cap g k α) := by
  rw [eqMp_chowGroup, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  · exact (c.cap_transport_eq g (show k = k - 1 + 1 by ring) _ _ α).symm
  · ring

end Transport

/-! ### Base change of a test scheme along an isomorphism -/

/-- An isomorphism `u : T' ⟶ T` of test schemes over `Y` induces an isomorphism of the two base
changes of `f : X ⟶ Y`. -/
def testBaseChangeIso {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (u : T' ⟶ T) [IsIso u]
    (m : T' ⟶ Y) (hm : u ≫ g = m) : pullback f m ≅ pullback f g where
  hom := pullback.map f m f g (𝟙 X) u (𝟙 Y) (by simp) (by simp [hm])
  inv := pullback.map f g f m (𝟙 X) (inv u) (𝟙 Y) (by simp) (by simp [← hm])
  hom_inv_id := by refine pullback.hom_ext ?_ ?_ <;> simp
  inv_hom_id := by refine pullback.hom_ext ?_ ?_ <;> simp

/-- The induced isomorphism of base changes lies over `X`. -/
@[reassoc (attr := simp)]
theorem testBaseChangeIso_hom_fst {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (u : T' ⟶ T)
    [IsIso u] (m : T' ⟶ Y) (hm : u ≫ g = m) :
    (testBaseChangeIso f g u m hm).hom ≫ pullback.fst f g = pullback.fst f m := by
  simp [testBaseChangeIso]

/-- The induced isomorphism of base changes lies over `u`. -/
@[reassoc (attr := simp)]
theorem testBaseChangeIso_hom_snd {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (u : T' ⟶ T)
    [IsIso u] (m : T' ⟶ Y) (hm : u ≫ g = m) :
    (testBaseChangeIso f g u m hm).hom ≫ pullback.snd f g = pullback.snd f m ≫ u := by
  simp [testBaseChangeIso]

/-- **Stacks 0B76 (1) for an isomorphism of test schemes.** The cap operation of a bivariant
class commutes with proper pushforward along an isomorphism of test schemes, the structure
morphism of the source being presented by an equality. -/
theorem BivariantClass.cap_chowPushforwardOfIso {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (u : T' ⟶ T) [IsIso u] (m : T' ⟶ Y) [LocallyOfFiniteType m]
    (hm : u ≫ g = m) (qm : T' ⟶ C.S) [LocallyOfFiniteType qm] (hqm : qm = m ≫ sY) (k : ℤ)
    (hmb : u ≫ (g ≫ sY) = qm) (α : chowGroup C qm k) (α' : chowGroup C (m ≫ sY) k)
    (hα : chowGroupCongr C hqm k α = α') :
    c.cap g k (chowPushforwardOfIso C qm (g ≫ sY) u hmb k α) =
      chowPushforwardOfIso C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX)
        (testBaseChangeIso f g u m hm).hom (by simp) (k - p) (c.cap m k α') := by
  subst hα
  subst hqm
  exact c.proper_naturality_of_test_eq g u m hm (testBaseChangeIso f g u m hm).hom
    (IsPullback.of_vert_isIso ⟨by simp⟩) (by simp) k hmb
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C (m ≫ sY) (g ≫ sY) u hmb k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C (pullback.fst f m ≫ sX)
      (pullback.fst f g ≫ sX) (testBaseChangeIso f g u m hm).hom (by simp) (k - p)) α

/-- **Stacks 0B6Y for a Gysin system.** The Gysin maps of the two readings of a section pulled
back in two steps agree, for a morphism presented as a composite. -/
theorem GysinSystem.onChow_pullbackComp {C : ChowSituation.{u}} {G : GysinSystem C}
    (hG : G.IsNaturalUnderPullbackCompPushforward) {A B T : Scheme.{u}} (q₁ : A ⟶ B)
    (q₂ : B ⟶ T) (q : A ⟶ T) (hq : q₁ ≫ q₂ = q) (pA : A ⟶ C.S) [LocallyOfFiniteType pA]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (α : chowGroup C pA (k + 1)) :
    chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q₁).obj
          ((Scheme.Modules.pullback q₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q₂ L s))).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q L s)).subschemeι ≫ pA)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (Stacks.Divisors.zeroScheme_pullback_comp_eq q₁ q₂ q hq L s)))
        (by
          rw [← Category.assoc,
            subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_eq q₁ q₂ q hq L s)]) k
        (G.onChow pA ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) k α) =
      G.onChow pA ((Scheme.Modules.pullback q).obj L)
        (AlgebraicGeometry.pullbackGlobalSections q L s) k α := by
  subst hq
  exact hG q₁ q₂ pA L s k α

/-! ### The triple of Definition 02T8 -/

section Triple

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The closed immersion `i : D ⟶ X` of the triple of Definition 02T8: the inclusion of the zero
scheme of `s`. -/
abbrev gysinTripleInclusion : (Stacks.Divisors.zeroScheme X L s).subscheme ⟶ X :=
  (Stacks.Divisors.zeroScheme X L s).subschemeι

/-- The pullback of the invertible module `L` to a test scheme. -/
abbrev gysinTripleModule {T : Scheme.{u}} (g : T ⟶ X) : T.Modules :=
  (Scheme.Modules.pullback g).obj L

/-- The pullback of the section `s` to a test scheme. -/
abbrev gysinTripleSection {T : Scheme.{u}} (g : T ⟶ X) : Γ(gysinTripleModule L g, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections g L s

/-- The divisor `D` base changed to a test scheme `g : T ⟶ X`: by Stacks 0B6Y it is the zero
scheme of the pulled-back section. -/
abbrev gysinTripleDivisor {T : Scheme.{u}} (g : T ⟶ X) : T.IdealSheafData :=
  Stacks.Divisors.zeroScheme T (gysinTripleModule L g) (gysinTripleSection L s g)

/-- The divisor `D` base changed to a test scheme `g : T ⟶ X` and then along `q : W ⟶ T`: the
zero scheme of the section pulled back in two steps. -/
abbrev gysinTripleDivisorIterated {T W : Scheme.{u}} (g : T ⟶ X) (q : W ⟶ T) :
    W.IdealSheafData :=
  Stacks.Divisors.zeroScheme W ((Scheme.Modules.pullback q).obj (gysinTripleModule L g))
    (AlgebraicGeometry.pullbackGlobalSections q (gysinTripleModule L g)
      (gysinTripleSection L s g))

/-- **Stacks 0B6Y.** The base change `D ×_X T` of the divisor along a test scheme `g : T ⟶ X` is
the zero scheme of the pulled-back section. -/
def gysinDivisorBaseChangeIso {T : Scheme.{u}} (g : T ⟶ X) :
    (gysinTripleDivisor L s g).subscheme ≅ pullback (gysinTripleInclusion L s) g :=
  (zeroSchemeFibreProductIso g L s).trans
    (pullbackSymmetry g (Stacks.Divisors.zeroScheme X L s).subschemeι)

/-- The identification of Stacks 0B6Y lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem gysinDivisorBaseChangeIso_hom_snd {T : Scheme.{u}} (g : T ⟶ X) :
    (gysinDivisorBaseChangeIso L s g).hom ≫ pullback.snd (gysinTripleInclusion L s) g =
      (gysinTripleDivisor L s g).subschemeι := by
  simp [gysinDivisorBaseChangeIso]

/-- The identification of Stacks 0B6Y carries the base-changed divisor into `X` as the
pulled-back divisor does. -/
theorem gysinDivisorBaseChangeIso_hom_comp_test {T : Scheme.{u}} (g : T ⟶ X) :
    (gysinDivisorBaseChangeIso L s g).hom ≫
        (pullback.fst (gysinTripleInclusion L s) g ≫ gysinTripleInclusion L s) =
      (gysinTripleDivisor L s g).subschemeι ≫ g := by
  rw [← Category.assoc, Category.assoc ((gysinDivisorBaseChangeIso L s g).hom),
    pullback.condition, ← Category.assoc, gysinDivisorBaseChangeIso_hom_snd]

/-- The identification of Stacks 0B6Y is compatible with the structure morphisms over the
base. -/
theorem gysinDivisorBaseChangeIso_hom_comp_structureMorphism (C : ChowSituation.{u})
    (sX : X ⟶ C.S) {T : Scheme.{u}} (g : T ⟶ X) :
    (gysinDivisorBaseChangeIso L s g).hom ≫
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) =
      (gysinTripleDivisor L s g).subschemeι ≫ (g ≫ sX) := by
  simpa using gysinDivisorBaseChangeIso_hom_comp_test L s g =≫ sX

/-- **Stacks 0B6Y for a two-leg base change.** The identification of the base change of the
divisor along `D ×_X T ⟶ T ⟶ X` with the zero scheme of the section pulled back to `Z ×_X T` is
compatible with the structure morphisms over the base. This is the hypothesis `hbase` of
`Stacks.Chow.BivariantClass.gysin_naturality`. -/
theorem bivariantDivisorBaseChangeIso_comp_structureMorphism (C : ChowSituation.{u})
    (sX : X ⟶ C.S) {Z T : Scheme.{u}} (f : Z ⟶ X) (t : T ⟶ X) :
    (bivariantDivisorBaseChangeIso f t (gysinTripleModule L t)
          (gysinTripleSection L s t)).hom ≫
        ((gysinTripleDivisorIterated L s t (pullback.snd f t)).subschemeι ≫
          (pullback.fst f t ≫ (f ≫ sX))) =
      pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX) := by
  rw [← Category.assoc, ← Category.assoc,
    bivariantDivisorBaseChangeIso_hom_subschemeι f t (gysinTripleModule L t)
      (gysinTripleSection L s t)]
  simp [bivariantBaseChangeMap]

/-- The two routes from the zero scheme of the twice pulled-back section to `Z ×_X (D ×_X T)`
agree: identifying it with the base change `Z ×_X (D ×_X T)` of the divisor directly, or reading
it as the base change of the divisor along `Z ×_X T ⟶ X`, identifying that with `D ×_X (Z ×_X T)`
by Stacks 0B6Y and then exchanging the two factors. -/
theorem bivariantDivisorBaseChangeIso_comp_commuteComparisonHom {Z T : Scheme.{u}} (f : Z ⟶ X)
    (t : T ⟶ X) :
    ((bivariantDivisorBaseChangeIso f t (gysinTripleModule L t)
            (gysinTripleSection L s t)).hom ≫
          eqToHom (congrArg Scheme.IdealSheafData.subscheme
            (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd f t) t
              (pullback.fst f t ≫ f) pullback.condition.symm L s))) ≫
        ((gysinDivisorBaseChangeIso L s (pullback.fst f t ≫ f)).hom ≫
          commuteComparisonHom (gysinTripleInclusion L s) f t) =
      (testBaseChangeIso f
        (pullback.fst (gysinTripleInclusion L s) t ≫ gysinTripleInclusion L s)
        (gysinDivisorBaseChangeIso L s t).hom
        ((gysinTripleDivisor L s t).subschemeι ≫ t)
        (gysinDivisorBaseChangeIso_hom_comp_test L s t)).hom := by
  have h1 := subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_eq
    (pullback.snd f t) t (pullback.fst f t ≫ f) pullback.condition.symm L s)
  have h2 := bivariantDivisorBaseChangeIso_hom_subschemeι f t (gysinTripleModule L t)
    (gysinTripleSection L s t)
  refine pullback.hom_ext ?_
    ((cancel_mono (pullback.snd (gysinTripleInclusion L s) t)).mp ?_) <;>
  simp [bivariantBaseChangeMap, reassoc_of% h1, reassoc_of% h2]

end Triple

/-! ### The cap operation of the bivariant Gysin class -/

section Cap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The cap operation of the bivariant Gysin class of Stacks 0B79: on a test scheme
`g : T ⟶ X` it is the Gysin map of the pulled-back section, read on the base change `D ×_X T` of
the divisor through the identification of Stacks 0B6Y. -/
def gysinBivariantCap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+
      chowGroup C (pullback.fst (gysinTripleInclusion L s) g ≫
        (gysinTripleInclusion L s ≫ sX)) (k - 1) :=
  (chowPushforwardOfIso C ((gysinTripleDivisor L s g).subschemeι ≫ (g ≫ sX))
      (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX))
      (gysinDivisorBaseChangeIso L s g).hom
      (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g) (k - 1)).comp
    ((G.onChow (g ≫ sX) (gysinTripleModule L g) (gysinTripleSection L s g) (k - 1)).comp
      (chowGroupDegreeEquiv C (g ≫ sX) (by ring : k = (k - 1) + 1)).toAddMonoidHom)

/-- The cap operation of the bivariant Gysin class, on a class. -/
theorem gysinBivariantCap_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    gysinBivariantCap C G sX L s g k α =
      chowPushforwardOfIso C ((gysinTripleDivisor L s g).subschemeι ≫ (g ≫ sX))
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX))
        (gysinDivisorBaseChangeIso L s g).hom
        (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L s C sX g) (k - 1)
        (G.onChow (g ≫ sX) (gysinTripleModule L g) (gysinTripleSection L s g) (k - 1)
          (chowGroupDegreeEquiv C (g ≫ sX) (by ring : k = (k - 1) + 1) α)) :=
  rfl

/-- **The characterization of Stacks 0B79.** A bivariant class of degree one for the closed
immersion `i : D ⟶ X` of the triple is *the* bivariant Gysin class when its cap operation is the
Gysin map of the pulled-back section on every test scheme. By
`Stacks.Chow.BivariantClass.ext` there is at most one such class. -/
def IsGysinBivariantClass
    (c' : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s)
      rfl 1) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k),
    c'.cap g k α = gysinBivariantCap C G sX L s g k α

/-! ### The commutation of Stacks 0FA3 -/

section Commute

variable {Z : Scheme.{u}} (f : Z ⟶ X) [LocallyOfFiniteType f] (p : ℤ)

/-- **Condition (3) of Stacks 0B76 at the divisor pulled back to a test scheme.** Capping with
`c` carries the Gysin class of `α` on `T` to the Gysin class of `c ∩ α` on `Z ×_X T`, read in
the degree `(k - p) - 1` that the commutation of Stacks 0FA2 uses. -/
theorem BivariantClass.gysin_naturality_baseChangeDivisor
    (c : BivariantClass C G (f ≫ sX) sX f rfl p) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowPushforwardOfIso C
        (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
        ((gysinTripleDivisorIterated L s t (pullback.snd f t)).subschemeι ≫
          (pullback.fst f t ≫ (f ≫ sX)))
        (bivariantDivisorBaseChangeIso f t (gysinTripleModule L t)
          (gysinTripleSection L s t)).hom
        (bivariantDivisorBaseChangeIso_comp_structureMorphism L s C sX f t) (k - p - 1)
        (chowGroupDegreeEquiv C
          (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
          (show k - 1 - p = k - p - 1 by ring)
          (c.cap ((gysinTripleDivisor L s t).subschemeι ≫ t) (k - 1)
            (G.onChow (t ≫ sX) (gysinTripleModule L t) (gysinTripleSection L s t) (k - 1)
              (chowGroupDegreeEquiv C (t ≫ sX) (show k = k - 1 + 1 by ring) α)))) =
      G.onChow ((pullback.fst f t ≫ f) ≫ sX)
        ((Scheme.Modules.pullback (pullback.snd f t)).obj (gysinTripleModule L t))
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f t) (gysinTripleModule L t)
          (gysinTripleSection L s t)) (k - p - 1)
        (chowGroupDegreeEquiv C ((pullback.fst f t ≫ f) ≫ sX)
          (show k - p = k - p - 1 + 1 by ring)
          (chowGroupCongr C (Category.assoc (pullback.fst f t) f sX).symm (k - p)
            (c.cap t k α))) := by
  have hgn := c.gysin_naturality t (gysinTripleModule L t) (gysinTripleSection L s t) (k - 1)
    (bivariantDivisorBaseChangeIso f t (gysinTripleModule L t) (gysinTripleSection L s t))
    (bivariantDivisorBaseChangeIso_hom_subschemeι f t (gysinTripleModule L t)
      (gysinTripleSection L s t))
    (bivariantDivisorBaseChangeIso_comp_structureMorphism L s C sX f t)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (chowGroupDegreeEquiv C (t ≫ sX) (show k = k - 1 + 1 by ring) α)
  rw [properChowPushforward_eq_chowPushforwardOfIso] at hgn
  have hk : k - 1 - p = k - p - 1 := by ring
  refine (chowGroupDegreeEquiv_chowPushforwardOfIso C
    (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
    ((gysinTripleDivisorIterated L s t (pullback.snd f t)).subschemeι ≫
      (pullback.fst f t ≫ (f ≫ sX)))
    (bivariantDivisorBaseChangeIso f t (gysinTripleModule L t) (gysinTripleSection L s t)).hom
    (bivariantDivisorBaseChangeIso_comp_structureMorphism L s C sX f t)
    hk _).symm.trans ?_
  rw [hgn, G.onChow_chowGroupDegreeEquiv _ _ _ hk (congrArg (· + 1) hk),
    c.cap_gysin_degree_transport t k α]
  exact rfl

/-- **Condition (3) of Stacks 0B76 read through Stacks 0B6Y.** Capping with `c` carries the
Gysin class of `α` on `T` to the Gysin class of `c ∩ α` on `Z ×_X T`, the base change of the
divisor being identified with the zero scheme of the section pulled back along
`Z ×_X T ⟶ X` in one step. -/
theorem BivariantClass.gysin_naturality_gysinCap
    (hG : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G (f ≫ sX) sX f rfl p) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowPushforwardOfIso C
        (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
        ((gysinTripleDivisor L s (pullback.fst f t ≫ f)).subschemeι ≫
          ((pullback.fst f t ≫ f) ≫ sX))
        ((bivariantDivisorBaseChangeIso f t (gysinTripleModule L t)
              (gysinTripleSection L s t)).hom ≫
          eqToHom (congrArg Scheme.IdealSheafData.subscheme
            (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd f t) t
              (pullback.fst f t ≫ f) pullback.condition.symm L s)))
        (by
          rw [Category.assoc, ← Category.assoc (eqToHom _),
            subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd f t) t
              (pullback.fst f t ≫ f) pullback.condition.symm L s)]
          exact bivariantDivisorBaseChangeIso_comp_structureMorphism L s C sX f t) (k - p - 1)
        (chowGroupDegreeEquiv C
          (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
          (show k - 1 - p = k - p - 1 by ring)
          (c.cap ((gysinTripleDivisor L s t).subschemeι ≫ t) (k - 1)
            (G.onChow (t ≫ sX) (gysinTripleModule L t) (gysinTripleSection L s t) (k - 1)
              (chowGroupDegreeEquiv C (t ≫ sX) (show k = k - 1 + 1 by ring) α)))) =
      G.onChow ((pullback.fst f t ≫ f) ≫ sX)
        (gysinTripleModule L (pullback.fst f t ≫ f))
        (gysinTripleSection L s (pullback.fst f t ≫ f)) (k - p - 1)
        (chowGroupDegreeEquiv C ((pullback.fst f t ≫ f) ≫ sX)
          (show k - p = k - p - 1 + 1 by ring)
          (chowGroupCongr C (Category.assoc (pullback.fst f t) f sX).symm (k - p)
            (c.cap t k α))) := by
  rw [← chowPushforwardOfIso_comp_apply C _ _ _
      (bivariantDivisorBaseChangeIso f t (gysinTripleModule L t)
        (gysinTripleSection L s t)).hom
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd f t) t
          (pullback.fst f t ≫ f) pullback.condition.symm L s)))
      (bivariantDivisorBaseChangeIso_comp_structureMorphism L s C sX f t)
      (by
        rw [← Category.assoc,
          subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_eq (pullback.snd f t) t
            (pullback.fst f t ≫ f) pullback.condition.symm L s)]
        exact rfl) (k - p - 1) _,
    c.gysin_naturality_baseChangeDivisor C G sX L s f p t k α]
  exact G.onChow_pullbackComp hG (pullback.snd f t) t (pullback.fst f t ≫ f)
    pullback.condition.symm ((pullback.fst f t ≫ f) ≫ sX) L s (k - p - 1) _

/-- The iterated cap operation `c ∩ (c' ∩ -)` of Stacks 0FA2, for `c'` the bivariant Gysin
class: pushing the Gysin class of `α` forward to `D ×_X T` and capping with `c` is capping with
`c` on the zero scheme of the pulled-back section. -/
theorem chowGroupDegreeEquiv_bivariantIteratedCap_gysin
    (c : BivariantClass C G (f ≫ sX) sX f rfl p)
    (c' : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl 1)
    (hc' : IsGysinBivariantClass C G sX L s c') {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowGroupDegreeEquiv C
        (pullback.fst f (pullback.fst (gysinTripleInclusion L s) t ≫
          gysinTripleInclusion L s) ≫ (f ≫ sX)) (show k - 1 - p = k - p - 1 by ring)
        (bivariantIteratedCap C G sX f (gysinTripleInclusion L s) p 1 c c' t k α) =
      chowPushforwardOfIso C
        (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
        (pullback.fst f (pullback.fst (gysinTripleInclusion L s) t ≫
          gysinTripleInclusion L s) ≫ (f ≫ sX))
        (testBaseChangeIso f
          (pullback.fst (gysinTripleInclusion L s) t ≫ gysinTripleInclusion L s)
          (gysinDivisorBaseChangeIso L s t).hom
          ((gysinTripleDivisor L s t).subschemeι ≫ t)
          (gysinDivisorBaseChangeIso_hom_comp_test L s t)).hom (by simp) (k - p - 1)
        (chowGroupDegreeEquiv C
          (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
          (show k - 1 - p = k - p - 1 by ring)
          (c.cap ((gysinTripleDivisor L s t).subschemeι ≫ t) (k - 1)
            (G.onChow (t ≫ sX) (gysinTripleModule L t) (gysinTripleSection L s t) (k - 1)
              (chowGroupDegreeEquiv C (t ≫ sX) (show k = k - 1 + 1 by ring) α)))) := by
  rw [bivariantIteratedCap_apply, hc', gysinBivariantCap_apply,
    chowGroupCongr_chowPushforwardOfIso_target,
    c.cap_chowPushforwardOfIso _ (gysinDivisorBaseChangeIso L s t).hom _
      (gysinDivisorBaseChangeIso_hom_comp_test L s t) _
      (Category.assoc (gysinTripleDivisor L s t).subschemeι t sX).symm (k - 1) _ _ _ rfl,
    chowGroupDegreeEquiv_chowPushforwardOfIso]
  · exact rfl
  · rw [← Category.assoc, gysinDivisorBaseChangeIso_hom_comp_test, Category.assoc]

/-- The iterated cap operation `c' ∩ (c ∩ -)` of Stacks 0FA2, for `c'` the bivariant Gysin
class: the Gysin class of `c ∩ α` on `Z ×_X T`, pushed forward to `Z ×_X (D ×_X T)`, is capping
with `c` on the zero scheme of the pulled-back section. -/
theorem chowPushforwardOfIso_bivariantIteratedCap_gysin
    (hG : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G (f ≫ sX) sX f rfl p)
    (c' : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl 1)
    (hc' : IsGysinBivariantClass C G sX L s c') {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowPushforwardOfIso C
        (pullback.fst (gysinTripleInclusion L s) (pullback.fst f t ≫ f) ≫
          (gysinTripleInclusion L s ≫ sX))
        (pullback.fst f (pullback.fst (gysinTripleInclusion L s) t ≫
          gysinTripleInclusion L s) ≫ (f ≫ sX))
        (commuteComparisonHom (gysinTripleInclusion L s) f t)
        (commuteComparisonHom_comp_structureMorphism C sX (gysinTripleInclusion L s) f t)
        (k - p - 1)
        (bivariantIteratedCap C G sX (gysinTripleInclusion L s) f 1 p c' c t k α) =
      chowPushforwardOfIso C
        (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
        (pullback.fst f (pullback.fst (gysinTripleInclusion L s) t ≫
          gysinTripleInclusion L s) ≫ (f ≫ sX))
        (testBaseChangeIso f
          (pullback.fst (gysinTripleInclusion L s) t ≫ gysinTripleInclusion L s)
          (gysinDivisorBaseChangeIso L s t).hom
          ((gysinTripleDivisor L s t).subschemeι ≫ t)
          (gysinDivisorBaseChangeIso_hom_comp_test L s t)).hom (by simp) (k - p - 1)
        (chowGroupDegreeEquiv C
          (pullback.fst f ((gysinTripleDivisor L s t).subschemeι ≫ t) ≫ (f ≫ sX))
          (show k - 1 - p = k - p - 1 by ring)
          (c.cap ((gysinTripleDivisor L s t).subschemeι ≫ t) (k - 1)
            (G.onChow (t ≫ sX) (gysinTripleModule L t) (gysinTripleSection L s t) (k - 1)
              (chowGroupDegreeEquiv C (t ≫ sX) (show k = k - 1 + 1 by ring) α)))) := by
  rw [bivariantIteratedCap_apply, hc', gysinBivariantCap_apply,
    ← c.gysin_naturality_gysinCap C G sX L s f p hG t k α,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _
    (bivariantDivisorBaseChangeIso_comp_commuteComparisonHom L s f t) _ _ _ _

/-- **Stacks 0FA3.** Let `(𝓛, s, i : D ⟶ X)` be a triple as in Definition 02T8, let
`f : Z ⟶ X` be locally of finite type and let `c ∈ A^p(Z ⟶ X)` be a bivariant class. Then the
bivariant Gysin class `c' ∈ A^1(D ⟶ X)` of Stacks 0B79 commutes with `c` in the sense of
Stacks 0FA2.

This is a restatement of condition (3) of Definition 0B76: the two iterated cap operations are
the two sides of `Stacks.Chow.BivariantClass.gysin_naturality` for `c` at the divisor pulled
back to the test scheme. -/
@[stacks 0FA3]
theorem gysinBivariantCommute (hG : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G (f ≫ sX) sX f rfl p)
    (c' : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl 1)
    (hc' : IsGysinBivariantClass C G sX L s c') :
    BivariantCommute C G sX (gysinTripleInclusion L s) f 1 p c' c := by
  intro T t _ k α
  exact (chowPushforwardOfIso_bivariantIteratedCap_gysin C G sX L s f p hG c c' hc' t k α).trans
    (chowGroupDegreeEquiv_bivariantIteratedCap_gysin C G sX L s f p c c' hc' t k α).symm

end Commute

end Cap

end Stacks.Chow

end
