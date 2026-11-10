module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward

/-!
# Bivariant Chow classes (Stacks 0B76)

Let `(S, δ)` be as in Situation 02QL, let `f : X ⟶ Y` be a morphism of schemes locally of finite
type over `S` and let `p ∈ ℤ`. A *bivariant class `c` of degree `p` for `f`* assigns to every
morphism `Y' ⟶ Y` locally of finite type and every `k` a map

  `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(X')`,  `X' = Y' ×_Y X`,

such that

1. for `Y'' ⟶ Y'` proper, `c ∩ (Y'' ⟶ Y')_* α'' = (X'' ⟶ X')_* (c ∩ α'')`;
2. for `Y'' ⟶ Y'` flat, locally of finite type, of relative dimension `r`,
   `c ∩ (Y'' ⟶ Y')^* α' = (X'' ⟶ X')^* (c ∩ α')`;
3. for an invertible module `L'` on `Y'` with a section `s'` and zero scheme `i' : D' ⟶ Y'`,
   with pullback `(N', t', j' : E' ⟶ X')` to `X'`, `c ∩ (i')^* α' = (j')^* (c ∩ α')`.

The collection of these is `A^p(X ⟶ Y)`.

## Main definitions

* `Stacks.Chow.BivariantChowClass` — a bivariant class of degree `p` for `f`. The operations are
  proper pushforward on Chow groups (Stacks 02S2), flat pullback on Chow groups (Stacks 02S1) and
  the Gysin map `i^*` of the zero scheme of a section of an invertible module (Stacks 02T8, 02TO),
  `Stacks.Chow.gysinChowOfInvertible`. The base-changed morphisms `X'' ⟶ X'` are the canonical
  maps `Stacks.Chow.bivariantBaseChangeMap`, and the identification `D' ×_Y X = E'` of
  Remark 0B6Y is the canonical isomorphism `Stacks.Chow.bivariantDivisorBaseChangeIso`.
* `Stacks.Chow.BivariantChowClass.capHom` — the cap operation as a homomorphism of groups.
* `Stacks.Chow.BivariantChowClass.equivBivariantClass` — a bivariant class is the same thing as a
  `Stacks.Chow.BivariantClass` at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the
  first Chern class.
* `Stacks.Chow.BivariantChowClass.addEquivBivariantClass` — that equivalence as an isomorphism of
  groups, for the abelian group structure on `A^p(X ⟶ Y)` whose operations are pointwise on cap
  products.

## Main results

* `Stacks.Chow.BivariantChowClass.cap_add` — the cap operations are additive.
* `Stacks.Chow.BivariantChowClass.cap_chowGroupRestrict` — the cap operations commute with
  restricting the test scheme along an open immersion.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The canonical map `X'' = Y'' ×_Y X ⟶ X' = Y' ×_Y X` over a morphism `Y'' ⟶ Y'` is a morphism
over the base. -/
theorem bivariantBaseChangeMap_comp_structureMorphism {S X Y T T' : Scheme.{u}} (sX : X ⟶ S)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) :
    bivariantBaseChangeMap f g h ≫ pullback.fst f g ≫ sX = pullback.fst f (h ≫ g) ≫ sX := by
  simp [bivariantBaseChangeMap]

/-- The canonical identification `D' ×_Y X = E'` of Remark 0B6Y is a morphism over the base. -/
theorem bivariantDivisorBaseChangeIso_hom_comp_structureMorphism {S X Y T : Scheme.{u}}
    (sX : X ⟶ S) (f : X ⟶ Y) (g : T ⟶ Y) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (bivariantDivisorBaseChangeIso f g L s).hom ≫
        ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          pullback.fst f g ≫ sX) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX := by
  rw [← Category.assoc, bivariantDivisorBaseChangeIso_hom_subschemeι,
    bivariantBaseChangeMap_comp_structureMorphism]

/-! ### Chow groups along a finite decomposition into open and closed pieces -/

section Pieces

variable (C : ChowSituation.{u})

/-- Pushing a cycle forward along an open immersion which is proper and restricting it back gives
the cycle. -/
theorem cycleGroupRestrict_properPushforward_self {Z A : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (m : A ⟶ Z)
    [IsOpenImmersion m] [IsProper m] (hm : m ≫ sZ = sA) (k : ℤ) (y : CycleGroup C sA k) :
    cycleGroupRestrict C sZ sA m hm k (properPushforward C sA sZ m hm k y) = y := by
  subst hm
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun z ↦ ?_
  rw [cycleGroupRestrict_apply, properPushforward_apply]
  have hpre : m.base ⁻¹' {m.base z} = {z} := by
    ext w
    simp [m.isOpenEmbedding.injective.eq_iff]
  rw [hpre, finsum_mem_singleton, relativeDimension_comp_isOpenImmersion,
    residueDegree_eq_one_of_isOpenImmersion]
  simp

/-- Pushing a cycle forward along a proper morphism and restricting it along an open immersion
with disjoint image gives zero. -/
theorem cycleGroupRestrict_properPushforward_of_disjoint {Z A A' : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A' ⟶ C.S)
    [LocallyOfFiniteType sA'] (m : A ⟶ Z) [IsProper m] (hm : m ≫ sZ = sA) (m' : A' ⟶ Z)
    [IsOpenImmersion m'] (hm' : m' ≫ sZ = sA')
    (hdisj : Disjoint (Set.range m.base) (Set.range m'.base)) (k : ℤ) (y : CycleGroup C sA k) :
    cycleGroupRestrict C sZ sA' m' hm' k (properPushforward C sA sZ m hm k y) = 0 := by
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun z ↦ ?_
  rw [cycleGroupRestrict_apply, properPushforward_apply]
  have hpre : m.base ⁻¹' {m'.base z} = ∅ :=
    Set.eq_empty_of_forall_notMem fun w hw ↦ Set.disjoint_left.mp hdisj ⟨w, rfl⟩ ⟨z, hw.symm⟩
  rw [hpre, finsum_mem_empty]
  rfl

/-- On Chow groups: restricting the pushforward along an open immersion which is proper back to
it is the identity. -/
theorem chowGroupRestrict_properChowPushforward_self {Z A : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (m : A ⟶ Z)
    [IsOpenImmersion m] [IsProper m] (hm : m ≫ sZ = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sZ m hm k)
    (y : chowGroup C sA k) :
    chowGroupRestrict C sZ sA m hm k (properChowPushforward C sA sZ m hm k hfac y) = y := by
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sA k))
      (cycleGroupRestrict_properPushforward_self C sZ sA m hm k c)

/-- On Chow groups: restricting a pushforward along an open immersion with disjoint image gives
zero. -/
theorem chowGroupRestrict_properChowPushforward_of_disjoint {Z A A' : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (m : A ⟶ Z) [IsProper m] (hm : m ≫ sZ = sA)
    (m' : A' ⟶ Z) [IsOpenImmersion m'] (hm' : m' ≫ sZ = sA')
    (hdisj : Disjoint (Set.range m.base) (Set.range m'.base)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sZ m hm k)
    (y : chowGroup C sA k) :
    chowGroupRestrict C sZ sA' m' hm' k (properChowPushforward C sA sZ m hm k hfac y) = 0 := by
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sA' k))
      (cycleGroupRestrict_properPushforward_of_disjoint C sZ sA sA' m hm m' hm' hdisj k c)

/-- For a finite family of pairwise disjoint open immersions which are proper, restricting a sum of
pushforwards along the `j`-th member picks out the `j`-th summand. -/
theorem chowGroupRestrict_sum_properChowPushforward {Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] {I : Type*} [Fintype I] {W : I → Scheme.{u}}
    (s : ∀ i, W i ⟶ C.S) [∀ i, LocallyOfFiniteType (s i)] (m : ∀ i, W i ⟶ Z)
    [∀ i, IsOpenImmersion (m i)] [∀ i, IsProper (m i)] (hm : ∀ i, m i ≫ sZ = s i)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (m i).base) (Set.range (m j).base))
    (k : ℤ) (y : ∀ i, chowGroup C (s i) k) (j : I) :
    chowGroupRestrict C sZ (s j) (m j) (hm j) k
        (∑ i, properChowPushforward C (s i) sZ (m i) (hm i) k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hm i) k)
          (y i)) = y j := by
  classical
  rw [map_sum, Finset.sum_eq_single j (fun i _ hij ↦
      chowGroupRestrict_properChowPushforward_of_disjoint C sZ (s i) (s j) (m i) (hm i) (m j)
        (hm j) (hdisj hij) k _ (y i)) (by simp),
    chowGroupRestrict_properChowPushforward_self]

/-- Pushforward along a morphism equal to the identity, after transporting along an equality of
structure morphisms, is the identity. -/
theorem properChowPushforward_chowGroupCongr_of_eq_id {A : Scheme.{u}} {sA sB : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (hBA : sB = sA) (v : A ⟶ A) (hv1 : v = 𝟙 A)
    [IsProper v] (hv : v ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB v hv k)
    (y : chowGroup C sB k) :
    properChowPushforward C sA sB v hv k hfac (chowGroupCongr C hBA k y) = y := by
  subst hv1 hBA
  exact DFunLike.congr_fun (properChowPushforward_id C sB k hfac) y

end Pieces

/-! ### Bivariant classes -/

/-- A bivariant class `c` of degree `p` for `f : X ⟶ Y`: a rule assigning to
every morphism `g : Y' ⟶ Y` locally of finite type and every `k` a map
`c ∩ - : CH_k(Y') ⟶ CH_{k-p}(X')`, `X' = Y' ×_Y X`, such that

1. for `h : Y'' ⟶ Y'` proper, `c ∩ h_* α'' = h'_* (c ∩ α'')`, `h' : X'' ⟶ X'` its base change;
2. for `h : Y'' ⟶ Y'` flat, locally of finite type, of relative dimension `r`,
   `c ∩ h^* α' = (h')^* (c ∩ α')`;
3. for an invertible module `L` on `Y'` with a global section `s`, zero scheme
   `i : D = Z(s) ⟶ Y'`, and pullback `(L', s', j : E = Z(s') ⟶ X')` to `X'`,
   `c ∩ i^* α' = j^* (c ∩ α')`, the scheme `D ×_Y X` being identified with `E` by Remark 0B6Y.

The group of all of them is `A^p(X ⟶ Y)`. -/
@[stacks 0B76 "a bivariant class of degree p for f, the elements of A^p(X → Y)"]
structure BivariantChowClass (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (p : ℤ) where
  /-- The map `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(Y' ×_Y X)` for a test morphism `g : Y' ⟶ Y`. -/
  cap : ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (g ≫ sY) k → chowGroup C (pullback.fst f g ≫ sX) (k - p)
  /-- Condition (1): compatibility with proper pushforward. -/
  cap_properPushforward : ∀ {Y' Y'' : Scheme.{u}} (g : Y' ⟶ Y) [LocallyOfFiniteType g]
      (h : Y'' ⟶ Y') [IsProper h] (k : ℤ) (α : chowGroup C ((h ≫ g) ≫ sY) k),
      cap g k (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc _ _ _).symm k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C ((h ≫ g) ≫ sY)
            (g ≫ sY) h (Category.assoc _ _ _).symm k) α) =
        properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
          (bivariantBaseChangeMap f g h)
          (bivariantBaseChangeMap_comp_structureMorphism sX f g h) (k - p)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
            (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g h)
            (bivariantBaseChangeMap_comp_structureMorphism sX f g h) (k - p))
          (cap (h ≫ g) k α)
  /-- Condition (2): compatibility with flat pullback of fixed relative dimension, as a
  heterogeneous equality between `CH_{(k + r) - p}` and `CH_{(k - p) + r}`. -/
  cap_flatPullback : ∀ {Y' Y'' : Scheme.{u}} (g : Y' ⟶ Y) [LocallyOfFiniteType g]
      (h : Y'' ⟶ Y') [LocallyOfFiniteType h] [Flat h] (r : ℕ)
      (hr : AlgebraicGeometry.RelativeDimension h r) (k : ℤ),
      letI : LocallyOfFiniteType (bivariantBaseChangeMap f g h) :=
        MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h)
          (P := @LocallyOfFiniteType) inferInstance
      letI : Flat (bivariantBaseChangeMap f g h) :=
        MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h) (P := @Flat)
          inferInstance
      ∀ (α : chowGroup C (g ≫ sY) k),
        HEq
          (cap (h ≫ g) (k + (r : ℤ))
            (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc _ _ _).symm r hr k
              (flatPullbackFactorsThroughRationalEquivalence_general C ((h ≫ g) ≫ sY) (g ≫ sY)
                h (Category.assoc _ _ _).symm r hr k) α))
          (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
            (bivariantBaseChangeMap f g h)
            (bivariantBaseChangeMap_comp_structureMorphism sX f g h) r
            (AlgebraicGeometry.RelativeDimension.of_isPullback
              (isPullback_bivariantBaseChangeMap f g h) hr) (k - p)
            (flatPullbackFactorsThroughRationalEquivalence_general C
              (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
              (bivariantBaseChangeMap f g h)
              (bivariantBaseChangeMap_comp_structureMorphism sX f g h) r
              (AlgebraicGeometry.RelativeDimension.of_isPullback
                (isPullback_bivariantBaseChangeMap f g h) hr) (k - p))
            (cap g k α))
  /-- Condition (3): compatibility with the Gysin map of the zero scheme of a section of an
  invertible module. -/
  cap_gysin : ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y) [LocallyOfFiniteType g] (L : Y'.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property L]
      (s : Γ(L, ⊤)) (k : ℤ) (α : chowGroup C (g ≫ sY) (k + 1)),
      properChowPushforward C
          (pullback.fst f ((Stacks.Divisors.zeroScheme Y' L s).subschemeι ≫ g) ≫ sX)
          ((Stacks.Divisors.zeroScheme (pullback f g)
            ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
            pullback.fst f g ≫ sX)
          (bivariantDivisorBaseChangeIso f g L s).hom
          (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism sX f g L s) (k - p)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism sX f g L s) (k - p))
          (cap ((Stacks.Divisors.zeroScheme Y' L s).subschemeι ≫ g) k
            (gysinChowOfInvertible C (g ≫ sY) k L s α)) =
        gysinChowOfInvertible C (pullback.fst f g ≫ sX) (k - p)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)
          (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
            (by omega : (k + 1) - p = (k - p) + 1)) (cap g (k + 1) α))

namespace BivariantChowClass

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} {hf : f ≫ sY = sX} {p : ℤ}

/-! ### The cap operations are additive -/

/-- The cap operations of a bivariant class at two degrees are carried to one another by a
heterogeneous equality of classes. -/
theorem heq_cap (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] {k l : ℤ} (hkl : k = l) {x : chowGroup C (g ≫ sY) k}
    {y : chowGroup C (g ≫ sY) l} (hxy : HEq x y) : HEq (c.cap g k x) (c.cap g l y) := by
  cases hkl
  exact heq_of_eq (congrArg (c.cap g k) (eq_of_heq hxy))

/-- The cap operation commutes with restricting the test scheme along an open immersion. -/
theorem cap_chowGroupRestrict (c : BivariantChowClass C sX sY f hf p) {T T' : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (v : T' ⟶ T) [IsOpenImmersion v] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    chowGroupRestrict C (pullback.fst f g ≫ sX) (pullback.fst f (v ≫ g) ≫ sX)
        (bivariantBaseChangeMap f g v) (bivariantBaseChangeMap_comp_structureMorphism sX f g v)
        (k - p) (c.cap g k α) =
      c.cap (v ≫ g) k
        (chowGroupRestrict C (g ≫ sY) ((v ≫ g) ≫ sY) v (Category.assoc _ _ _).symm k α) := by
  have hr : AlgebraicGeometry.RelativeDimension v 0 := relativeDimension_of_isOpenImmersion v
  have hr' : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap f g v) 0 :=
    relativeDimension_of_isOpenImmersion _
  refine eq_of_heq ((heq_chowGroupRestrict_flatPullbackChow C _ _ _
      (bivariantBaseChangeMap_comp_structureMorphism sX f g v) hr' (k - p)
      (flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C _ _ _
        (bivariantBaseChangeMap_comp_structureMorphism sX f g v) (k - p))
      (c.cap g k α)).trans ((c.cap_flatPullback g v 0 hr k α).symm.trans ?_))
  exact c.heq_cap (v ≫ g) (by simp)
    (heq_chowGroupRestrict_flatPullbackChow C _ _ v (Category.assoc _ _ _).symm hr k
      (flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C _ _ v
        (Category.assoc _ _ _).symm k) α).symm

/-- A test morphism equal to `g`, and a morphism over `X` between the two base changes lying over
the identity of the test scheme: pushforward along it carries the cap operation at the first test
morphism to the cap operation at `g`. -/
theorem properChowPushforward_cap_of_eq (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}}
    {g g' : T ⟶ Y} [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hg : g' = g)
    (hgY : g ≫ sY = g' ≫ sY) (v : pullback f g' ⟶ pullback f g) [IsProper v]
    (hvfst : v ≫ pullback.fst f g = pullback.fst f g')
    (hvsnd : v ≫ pullback.snd f g = pullback.snd f g')
    (hv : v ≫ pullback.fst f g ≫ sX = pullback.fst f g' ≫ sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f g' ≫ sX)
      (pullback.fst f g ≫ sX) v hv (k - p))
    (x : chowGroup C (g ≫ sY) k) :
    properChowPushforward C (pullback.fst f g' ≫ sX) (pullback.fst f g ≫ sX) v hv (k - p) hfac
        (c.cap g' k (chowGroupCongr C hgY k x)) = c.cap g k x := by
  subst hg
  obtain rfl : v = 𝟙 _ := pullback.hom_ext (by simpa using hvfst) (by simpa using hvsnd)
  exact DFunLike.congr_fun (properChowPushforward_id C _ (k - p) hfac) _

/-- The cap operation of a bivariant class is additive. -/
theorem cap_add (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α β : chowGroup C (g ≫ sY) k) :
    c.cap g k (α + β) = c.cap g k α + c.cap g k β := by
  classical
  let Z : ULift.{u} Bool → Scheme.{u} := fun _ ↦ T
  let ι : ∀ _ : ULift.{u} Bool, T ⟶ ∐ Z := fun i ↦ Sigma.ι Z i
  let ν : (∐ Z) ⟶ T := Sigma.desc fun _ ↦ 𝟙 T
  have hιν (i : ULift.{u} Bool) : ι i ≫ ν = 𝟙 T := Sigma.ι_comp_desc _ _
  have : ∀ i, IsOpenImmersion (ι i) := fun i ↦ inferInstanceAs (IsOpenImmersion (Sigma.ι Z i))
  have : ∀ i, IsClosedImmersion (ι i) := fun i ↦ isClosedImmersion_sigmaι Z i
  have : ∀ i, IsProper (ι i) := fun _ ↦ inferInstance
  have : IsProper ν := isProper_sigmaDesc_of_locallyFinite Z _ (locallyFinite_of_finite _)
  have hsum2 {M : Type u} [AddCommMonoid M] (F : ULift.{u} Bool → M) :
      ∑ i, F i = F ⟨true⟩ + F ⟨false⟩ := by
    rw [← Fintype.sum_equiv Equiv.ulift.symm (fun b ↦ F (Equiv.ulift.symm b)) F (fun _ ↦ rfl),
      Fintype.sum_bool]
    rfl
  let a : ULift.{u} Bool → chowGroup C (g ≫ sY) k := fun i ↦ if i.down then α else β
  have hg (i : ULift.{u} Bool) : ι i ≫ ν ≫ g = g := by
    rw [← Category.assoc, hιν, Category.id_comp]
  have hb (i : ULift.{u} Bool) : g ≫ sY = (ι i ≫ ν ≫ g) ≫ sY := by rw [hg i]
  let y : ∀ i, chowGroup C ((ι i ≫ ν ≫ g) ≫ sY) k := fun i ↦ chowGroupCongr C (hb i) k (a i)
  have hι (i : ULift.{u} Bool) : ι i ≫ (ν ≫ g) ≫ sY = (ι i ≫ ν ≫ g) ≫ sY := by
    simp only [Category.assoc]
  let γ : chowGroup C ((ν ≫ g) ≫ sY) k := ∑ i,
    properChowPushforward C ((ι i ≫ ν ≫ g) ≫ sY) ((ν ≫ g) ≫ sY) (ι i) (hι i) k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hι i) k) (y i)
  have hγ : properChowPushforward C ((ν ≫ g) ≫ sY) (g ≫ sY) ν (Category.assoc _ _ _).symm k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
        (Category.assoc _ _ _).symm k) γ = α + β := by
    have key (i : ULift.{u} Bool) :
        properChowPushforward C ((ν ≫ g) ≫ sY) (g ≫ sY) ν (Category.assoc _ _ _).symm k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (Category.assoc _ _ _).symm k)
          (properChowPushforward C ((ι i ≫ ν ≫ g) ≫ sY) ((ν ≫ g) ≫ sY) (ι i) (hι i) k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hι i) k)
            (y i)) = a i := by
      have hw : (ι i ≫ ν) ≫ g ≫ sY = (ι i ≫ ν ≫ g) ≫ sY := by simp only [Category.assoc]
      rw [← properChowPushforward_comp_apply C _ _ _ (ι i) ν (ι i ≫ ν) rfl (hι i)
        (Category.assoc _ _ _).symm hw k _ _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ hw k)]
      exact properChowPushforward_chowGroupCongr_of_eq_id C (hb i) (ι i ≫ ν) (hιν i) hw k _ _
    simp only [γ, map_sum]
    rw [hsum2, key, key]
    rfl
  let m : ∀ i, pullback f (ι i ≫ ν ≫ g) ⟶ pullback f (ν ≫ g) := fun i ↦
    bivariantBaseChangeMap f (ν ≫ g) (ι i)
  have hm (i : ULift.{u} Bool) : m i ≫ pullback.fst f (ν ≫ g) ≫ sX =
      pullback.fst f (ι i ≫ ν ≫ g) ≫ sX :=
    bivariantBaseChangeMap_comp_structureMorphism sX f (ν ≫ g) (ι i)
  have hrange (i : ULift.{u} Bool) :
      Set.range (m i).base = (pullback.snd f (ν ≫ g)).base ⁻¹' Set.range (ι i).base :=
    range_base_of_isPullback _ (m i) (ι i) _
      (isPullback_bivariantBaseChangeMap f (ν ≫ g) (ι i)).flip
  have hdisjι : Pairwise fun i j ↦ Disjoint (Set.range (ι i).base) (Set.range (ι j).base) :=
    pairwise_disjoint_range_sigmaι Z
  have hdisjm : Pairwise fun i j ↦ Disjoint (Set.range (m i).base) (Set.range (m j).base) :=
    fun i j hij ↦ by simpa only [hrange] using (hdisjι hij).preimage _
  have hdec : IsClopenDecomposition fun i ↦ (m i).opensRange :=
    isClopenDecomposition_of_isOpenImmersion_cover m
      (fun x ↦ by
        obtain ⟨i, hi⟩ := exists_mem_range_sigmaι Z ((pullback.snd f (ν ≫ g)).base x)
        exact ⟨i, by rwa [hrange]⟩)
      hdisjm
  have hcapγ : c.cap (ν ≫ g) k γ = ∑ i,
      properChowPushforward C (pullback.fst f (ι i ≫ ν ≫ g) ≫ sX)
        (pullback.fst f (ν ≫ g) ≫ sX) (m i) (hm i) (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hm i) (k - p))
        (c.cap (ι i ≫ ν ≫ g) k (y i)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_chowGroupRestrict_eq_zero C (pullback.fst f (ν ≫ g) ≫ sX)
      (fun i ↦ pullback.fst f (ι i ≫ ν ≫ g) ≫ sX) m hm hdec (k - p) _ fun j ↦ ?_
    rw [map_sub, sub_eq_zero, cap_chowGroupRestrict c (ν ≫ g) (ι j) k γ,
      chowGroupRestrict_sum_properChowPushforward C _ _ m hm hdisjm (k - p) _ j]
    congr 1
    exact chowGroupRestrict_sum_properChowPushforward C _ _ ι hι hdisjι k y j
  have hsum : ∑ i, c.cap g k (a i) = c.cap g k α + c.cap g k β := hsum2 _
  rw [← hγ, c.cap_properPushforward g ν k γ, hcapγ, map_sum, ← hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hv : (m i ≫ bivariantBaseChangeMap f g ν) ≫ pullback.fst f g ≫ sX =
      pullback.fst f (ι i ≫ ν ≫ g) ≫ sX := by
    simp [m, bivariantBaseChangeMap]
  rw [← properChowPushforward_comp_apply C _ _ _ (m i) (bivariantBaseChangeMap f g ν)
    (m i ≫ bivariantBaseChangeMap f g ν) rfl (hm i)
    (bivariantBaseChangeMap_comp_structureMorphism sX f g ν) hv (k - p) _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ hv (k - p))]
  exact c.properChowPushforward_cap_of_eq (hg i)
    (hb i) _ (by simp [m, bivariantBaseChangeMap])
    (by simp [m, bivariantBaseChangeMap, hιν i]) hv k _ (a i)

/-- The cap operation of a bivariant class as a homomorphism of groups. -/
def capHom (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - p) :=
  AddMonoidHom.mk' (c.cap g k) (c.cap_add g k)

/-- The homomorphism `capHom` evaluates to the cap operation of the bivariant class. -/
@[simp]
theorem capHom_apply (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    c.capHom g k α = c.cap g k α :=
  rfl

/-! ### Comparison with `Stacks.Chow.BivariantClass` -/

variable [LocallyOfFiniteType f]

omit [LocallyOfFiniteType f] in
/-- A morphism between two base changes of `f` making the defining square cartesian and lying
over `X` is the canonical one. -/
theorem eq_bivariantBaseChangeMap {T T' : Scheme.{u}} (g : T ⟶ Y) (h : T' ⟶ T)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) :
    h' = bivariantBaseChangeMap f g h := by
  refine pullback.hom_ext ?_ ?_
  · simp [bivariantBaseChangeMap, hfst]
  · simp [bivariantBaseChangeMap, sq.w]

omit [LocallyOfFiniteType f] in
/-- An identification of `D ×_Y X` with the zero scheme `E` lying over the canonical base-change
map is the canonical identification of Remark 0B6Y. -/
theorem eq_bivariantDivisorBaseChangeIso {T : Scheme.{u}} (g : T ⟶ Y) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : pullback f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι =
      bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L s).subschemeι) :
    e = bivariantDivisorBaseChangeIso f g L s := by
  refine Iso.ext ?_
  rw [← cancel_mono (Stacks.Divisors.zeroScheme (pullback f g)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι, he,
    bivariantDivisorBaseChangeIso_hom_subschemeι]

/-- The bivariant class underlying a `BivariantClass` at the Gysin system of the first Chern
class. -/
def ofBivariantClass (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    BivariantChowClass C sX sY f hf p where
  cap g _ k := c.cap g k
  cap_properPushforward g _ h _ k α :=
    c.cap_properPushforward g h (bivariantBaseChangeMap f g h)
      (isPullback_bivariantBaseChangeMap f g h)
      (by simp [bivariantBaseChangeMap]) k α
  cap_flatPullback g _ h _ _ r hr k α :=
    c.cap_flatPullbackChow g h r hr (bivariantBaseChangeMap f g h)
      (isPullback_bivariantBaseChangeMap f g h)
      (by simp [bivariantBaseChangeMap]) k α
  cap_gysin g _ L _ s k α :=
    c.cap_gysin g L s k (bivariantDivisorBaseChangeIso f g L s)
      (bivariantDivisorBaseChangeIso_hom_subschemeι f g L s)
      (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism sX f g L s) α

/-- The `BivariantClass` at the Gysin system of the first Chern class underlying a bivariant
class. -/
def toBivariantClass (c : BivariantChowClass C sX sY f hf p) :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p where
  cap g _ k := c.capHom g k
  cap_properPushforward g _ h _ h' sq hfst k α := by
    obtain rfl := eq_bivariantBaseChangeMap g h h' sq hfst
    exact c.cap_properPushforward g h k α
  cap_flatPullbackChow g _ h _ _ r hr h' sq hfst k α := by
    obtain rfl := eq_bivariantBaseChangeMap g h h' sq hfst
    exact c.cap_flatPullback g h r hr k α
  cap_gysin g _ L _ s k e he hbase α := by
    obtain rfl := eq_bivariantDivisorBaseChangeIso g L s e he
    exact c.cap_gysin g L s k α

/-- A bivariant class of degree `p` for `f` is the same thing as a `Stacks.Chow.BivariantClass`
at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class; the cap
operations correspond identically. -/
@[stacks 0B76 "bridge: A^p(X → Y) is BivariantClass at the Gysin system of the first Chern \
class"]
def equivBivariantClass :
    BivariantChowClass C sX sY f hf p ≃ BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p
    where
  toFun := toBivariantClass
  invFun := ofBivariantClass
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cap operations of the `BivariantClass` attached to a bivariant class are those of the
bivariant class. -/
@[simp]
theorem equivBivariantClass_cap (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    ⇑((equivBivariantClass c).cap g k) = c.cap g k :=
  rfl

/-- The cap operations of the bivariant class attached to a `BivariantClass` are those of the
`BivariantClass`. -/
@[simp]
theorem equivBivariantClass_symm_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    (equivBivariantClass.symm c).cap g k = ⇑(c.cap g k) :=
  rfl

/-- A bivariant class is determined by its cap operations. -/
@[ext]
theorem ext {c d : BivariantChowClass C sX sY f hf p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sY) k), c.cap g k α = d.cap g k α) : c = d :=
  equivBivariantClass.injective (BivariantClass.ext _ _ _ _ _ _ _ fun g _ k α ↦ h g k α)

/-! ### The group `A^p(X ⟶ Y)` -/

/-- Bivariant classes of degree `p` for `f` form an abelian group `A^p(X ⟶ Y)`, transported
along `Stacks.Chow.BivariantChowClass.equivBivariantClass`. -/
instance : AddCommGroup (BivariantChowClass C sX sY f hf p) :=
  equivBivariantClass.addCommGroup

/-- The equivalence `Stacks.Chow.BivariantChowClass.equivBivariantClass` as an isomorphism of
groups. -/
def addEquivBivariantClass :
    BivariantChowClass C sX sY f hf p ≃+ BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p
    :=
  equivBivariantClass.addEquiv

/-- The group isomorphism `addEquivBivariantClass` agrees with `equivBivariantClass`. -/
@[simp]
theorem addEquivBivariantClass_apply (c : BivariantChowClass C sX sY f hf p) :
    addEquivBivariantClass c = equivBivariantClass c :=
  rfl

/-- The cap operation of the zero bivariant class is zero. -/
@[simp]
theorem zero_cap {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    (0 : BivariantChowClass C sX sY f hf p).cap g k = 0 :=
  rfl

/-- The cap operation of a sum of bivariant classes is the sum of the cap operations. -/
@[simp]
theorem add_cap (c d : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) : (c + d).cap g k = c.cap g k + d.cap g k :=
  rfl

/-- The cap operation of the negative of a bivariant class is the negative of its cap
operation. -/
@[simp]
theorem neg_cap (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) : (-c).cap g k = -c.cap g k :=
  rfl

/-- The cap operation of a difference of bivariant classes is the difference of the cap
operations. -/
@[simp]
theorem sub_cap (c d : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) : (c - d).cap g k = c.cap g k - d.cap g k := by
  rw [sub_eq_add_neg c d, add_cap, neg_cap, ← sub_eq_add_neg]

end BivariantChowClass

end Stacks.Chow

end
