module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.DivisorFibreCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TripleProductAssociativity
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the triple intersection product, as cycles

Let `X` be a nonsingular variety and let `U`, `V`, `W ⊆ X` be closed subvarieties whose triple
intersection has dimension at most `m`. Section 43.20 of the source expands the two iterated
intersection products as the alternating double sums

`∑ᵢⱼ (-1)ⁱ⁺ʲ [Torᵢ(𝒪_U, Torⱼ(𝒪_V, 𝒪_W))]_m`  and  `∑ᵢⱼ (-1)ⁱ⁺ʲ [Torⱼ(Torᵢ(𝒪_U, 𝒪_V), 𝒪_W)]_m`

of cycles of iterated `Tor` sheaves, and proves them equal. This file constructs those two cycles
and proves that identity, for arbitrary coherent modules in place of the three structure sheaves.

## Main definitions

* `AlgebraicGeometry.TorFormula.iteratedTorSheafLeft` and
  `AlgebraicGeometry.TorFormula.iteratedTorSheafRight` — the sheaves `Torᵢ(ℱ, Torⱼ(𝒢, ℋ))` and
  `Torᵢ(Torⱼ(ℱ, 𝒢), ℋ)`.
* `AlgebraicGeometry.TorFormula.stalkTorModuleCatIso` — the stalk of a `Tor` sheaf, read over the
  local ring of the scheme, is the `Tor` module of the stalks.
* `AlgebraicGeometry.TorFormula.iteratedTorCycleLeft` and
  `AlgebraicGeometry.TorFormula.iteratedTorCycleRight` — the two alternating double sums.

## References

* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

variable {X : Scheme.{u}}

/-! ### The stalk of a `Tor` sheaf over the local ring of the scheme -/

/-- **The stalk of a `Tor` sheaf is the `Tor` module of the stalks**, as modules over the local
ring `𝒪_{X, x}`. This is the stalk clause of Tag 0AZT, carried across the comparison of the
`RingCat`-valued and `CommRingCat`-valued stalk rings; the length-only form of the same statement
is `AlgebraicGeometry.TorFormula.sheafMultiplicity_torSheaf_eq_length_tor_stalk`. -/
@[ega "III 6.5.7" "(i), special case"]
def stalkTorModuleCatIso (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) (x : X) :
    stalkModuleCat X (torSheaf X F G p) x ≅
      ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj (stalkModuleCat X F x)).obj
        (stalkModuleCat X G x) :=
  letI := StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  (stalkRestrictIso X (torSheaf X F G p) x).symm ≪≫
    (ModuleCat.restrictScalars (stalkRingEquiv X x).symm.toRingHom).mapIso
      (torSheafStalkIso X F G p x) ≪≫
    (RingTheory.TorIndependence.torRestrictIso (stalkRingEquiv X x).symm
      ((Scheme.Modules.stalkFunctor X x).obj F)
      ((Scheme.Modules.stalkFunctor X x).obj G) p).symm ≪≫
    ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).mapIso (stalkRestrictIso X F x)).app _ ≪≫
    ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj
      (stalkModuleCat X F x)).mapIso (stalkRestrictIso X G x)

/-! ### Iterated `Tor` sheaves -/

/-- The left-associated iterated `Tor` sheaf `Torₚ^{𝒪_X}(ℱ, Tor_q^{𝒪_X}(𝒢, ℋ))`. -/
def iteratedTorSheafLeft (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ) : X.Modules :=
  torSheaf X F (torSheaf X G H q) p

/-- The right-associated iterated `Tor` sheaf `Torₚ^{𝒪_X}(Tor_q^{𝒪_X}(ℱ, 𝒢), ℋ)`. -/
def iteratedTorSheafRight (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ) : X.Modules :=
  torSheaf X (torSheaf X F G q) H p

/-- On a regular scheme the left-associated iterated `Tor` sheaf of three coherent modules is
coherent. -/
theorem isCoherent_iteratedTorSheafLeft (X : Scheme.{u}) (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (p q : ℕ) :
    (iteratedTorSheafLeft X F G H p q).IsCoherent :=
  isCoherent_torSheaf_of_isRegular X hX F _ hF
    (isCoherent_torSheaf_of_isRegular X hX G H hG hH q) p

/-- On a regular scheme the right-associated iterated `Tor` sheaf of three coherent modules is
coherent. -/
theorem isCoherent_iteratedTorSheafRight (X : Scheme.{u}) (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (p q : ℕ) :
    (iteratedTorSheafRight X F G H p q).IsCoherent :=
  isCoherent_torSheaf_of_isRegular X hX _ H
    (isCoherent_torSheaf_of_isRegular X hX F G hF hG q) hH p

/-- A sheaf of modules which is a zero object has empty support. -/
theorem notMem_supp_of_isZero (F : X.Modules) (h : IsZero F) (x : X) :
    x ∉ SheafOfModules.supp F :=
  (Scheme.Modules.notMem_supp_iff_isZero_stalk F x).mpr
    (Functor.map_isZero (Scheme.Modules.stalkFunctor X x) h)

/-- The left-associated iterated `Tor` sheaf is supported on the triple intersection of the three
supports. -/
theorem supp_iteratedTorSheafLeft_subset (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ) :
    SheafOfModules.supp (iteratedTorSheafLeft X F G H p q) ⊆
      SheafOfModules.supp F ∩ SheafOfModules.supp G ∩ SheafOfModules.supp H := by
  intro x hx
  obtain ⟨hxF, hxT⟩ := supp_torSheaf_subset_inter X F (torSheaf X G H q) p hx
  obtain ⟨hxG, hxH⟩ := supp_torSheaf_subset_inter X G H q hxT
  exact ⟨⟨hxF, hxG⟩, hxH⟩

/-- The right-associated iterated `Tor` sheaf is supported on the triple intersection of the
three supports. -/
theorem supp_iteratedTorSheafRight_subset (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ) :
    SheafOfModules.supp (iteratedTorSheafRight X F G H p q) ⊆
      SheafOfModules.supp F ∩ SheafOfModules.supp G ∩ SheafOfModules.supp H := by
  intro x hx
  obtain ⟨hxT, hxH⟩ := supp_torSheaf_subset_inter X (torSheaf X F G q) H p hx
  obtain ⟨hxF, hxG⟩ := supp_torSheaf_subset_inter X F G q hxT
  exact ⟨⟨hxF, hxG⟩, hxH⟩

/-- The stalk of the left-associated iterated `Tor` sheaf is the left-associated iterated `Tor`
module of the three stalks. -/
def stalkIteratedTorLeftIso (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ) (x : X) :
    stalkModuleCat X (iteratedTorSheafLeft X F G H p q) x ≅
      ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj (stalkModuleCat X F x)).obj
        (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) q).obj (stalkModuleCat X G x)).obj
          (stalkModuleCat X H x)) :=
  stalkTorModuleCatIso X F (torSheaf X G H q) p x ≪≫
    ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj (stalkModuleCat X F x)).mapIso
      (stalkTorModuleCatIso X G H q x)

/-- The stalk of the right-associated iterated `Tor` sheaf is the right-associated iterated `Tor`
module of the three stalks. -/
def stalkIteratedTorRightIso (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ) (x : X) :
    stalkModuleCat X (iteratedTorSheafRight X F G H p q) x ≅
      ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj
          (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) q).obj (stalkModuleCat X F x)).obj
            (stalkModuleCat X G x))).obj (stalkModuleCat X H x) :=
  stalkTorModuleCatIso X (torSheaf X F G q) H p x ≪≫
    ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).mapIso
      (stalkTorModuleCatIso X F G q x)).app (stalkModuleCat X H x)

/-! ### The two alternating double sums of cycles -/

/-- The delta-dimension bounds under which the left-associated double sum is a sum of
`k`-cycles. -/
def IteratedTorSupportBoundLeft (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ) : Prop :=
  ∀ p q : ℕ,
    haveI := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH p q
    Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (iteratedTorSheafLeft X F G H p q)).subschemeι ≫ f) ≤
      WithBotTop.coe k

/-- The delta-dimension bounds under which the right-associated double sum is a sum of
`k`-cycles. -/
def IteratedTorSupportBoundRight (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ) : Prop :=
  ∀ p q : ℕ,
    haveI := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH p q
    Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (iteratedTorSheafRight X F G H p q)).subschemeι ≫ f) ≤
      WithBotTop.coe k

/-- The left-associated alternating double sum
`∑ₚ_q (-1)^(p+q) [Torₚ(ℱ, Tor_q(𝒢, ℋ))]_k` of cycles of iterated `Tor` sheaves. For `ℱ`, `𝒢`,
`ℋ` the structure sheaves of three closed subvarieties and `k` the expected dimension of the
triple intersection, this is the right-hand side of the first display of Section 43.20. -/
def iteratedTorCycleLeft (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hFk : IteratedTorSupportBoundLeft C f hX F G H hF hG hH k) : AlgebraicCycle X ℤ :=
  ∑ᶠ pq : ℕ × ℕ, ((-1 : ℤ) ^ (pq.1 + pq.2)) •
    (haveI := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH pq.1 pq.2
     Stacks.Chow.coherentSheafCycle C f (iteratedTorSheafLeft X F G H pq.1 pq.2) k
       (hFk pq.1 pq.2))

/-- The right-associated alternating double sum
`∑ₚ_q (-1)^(p+q) [Torₚ(Tor_q(ℱ, 𝒢), ℋ)]_k` of cycles of iterated `Tor` sheaves. -/
def iteratedTorCycleRight (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hFk : IteratedTorSupportBoundRight C f hX F G H hF hG hH k) : AlgebraicCycle X ℤ :=
  ∑ᶠ pq : ℕ × ℕ, ((-1 : ℤ) ^ (pq.1 + pq.2)) •
    (haveI := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH pq.1 pq.2
     Stacks.Chow.coherentSheafCycle C f (iteratedTorSheafRight X F G H pq.1 pq.2) k
       (hFk pq.1 pq.2))

/-! ### Vanishing above the dimension of the scheme -/

/-- Above the dimension of `X` the left-associated iterated `Tor` sheaf has empty support. -/
theorem notMem_supp_iteratedTorSheafLeft_of_lt (X : Scheme.{u})
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (F G H : X.Modules) (d p q : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdpq : d < p ∨ d < q) (x : X) :
    x ∉ SheafOfModules.supp (iteratedTorSheafLeft X F G H p q) := by
  rcases hdpq with hp | hq
  · exact notMem_supp_of_isZero _
      (isZero_torSheaf_of_lt X hreg F (torSheaf X G H q) d p hd hp) x
  · exact fun hx => notMem_supp_of_isZero _ (isZero_torSheaf_of_lt X hreg G H d q hd hq) x
      (supp_torSheaf_subset_inter X F (torSheaf X G H q) p hx).2

/-- Above the dimension of `X` the right-associated iterated `Tor` sheaf has empty support. -/
theorem notMem_supp_iteratedTorSheafRight_of_lt (X : Scheme.{u})
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (F G H : X.Modules) (d p q : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdpq : d < p ∨ d < q) (x : X) :
    x ∉ SheafOfModules.supp (iteratedTorSheafRight X F G H p q) := by
  rcases hdpq with hp | hq
  · exact notMem_supp_of_isZero _
      (isZero_torSheaf_of_lt X hreg (torSheaf X F G q) H d p hd hp) x
  · exact fun hx => notMem_supp_of_isZero _ (isZero_torSheaf_of_lt X hreg F G d q hd hq) x
      (supp_torSheaf_subset_inter X (torSheaf X F G q) H p hx).1

/-- The cycle of a coherent sheaf in a dimension its support does not reach is the zero cycle:
every coefficient of `[ℱ]_k` is read at a point of the support whose closure has
delta-dimension `k`. In particular the cycle of a sheaf with empty support is zero. -/
theorem coherentSheafCycle_eq_zero_of_relativeDimension_ne (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (k : ℤ)
    (hFk : Stacks.Chow.schemeDeltaDimension C ((Stacks.Chow.reducedSupport F).subschemeι ≫ f)
      ≤ WithBotTop.coe k)
    (h : ∀ z ∈ SheafOfModules.supp F,
      Stacks.Chow.relativeDimension C.dimensionFunction f z ≠ k) :
    Stacks.Chow.coherentSheafCycle C f F k hFk = 0 := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro z
  change Stacks.Chow.sheafCycleCoeff C f F k z = 0
  simp only [Stacks.Chow.sheafCycleCoeff, ite_eq_right_iff]
  exact fun hz => absurd hz.2 (h z hz.1)

/-- A zero object of `ModuleCat` has length zero. -/
private lemma length_eq_zero_of_isZero {A : Type u} [CommRing A] {M : ModuleCat.{u} A}
    (h : IsZero M) : Module.length A M = 0 :=
  have := ModuleCat.isZero_iff_subsingleton.mp h
  Module.length_eq_zero

/-- The stalk of a coherent sheaf at a point of delta-dimension `k` has finite length: such a
point is the generic point of an irreducible component of the support. -/
theorem length_stalk_ne_top_of_relativeDimension_eq (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (k : ℤ)
    (hFk : Stacks.Chow.schemeDeltaDimension C ((Stacks.Chow.reducedSupport F).subschemeι ≫ f)
      ≤ WithBotTop.coe k)
    {z : X} (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k) :
    Module.length (X.presheaf.stalk z) (F.presheaf.stalk z) ≠ ⊤ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [Module.length_ne_top_iff]
  by_cases hzs : z ∈ SheafOfModules.supp F
  · obtain ⟨Z, hZ⟩ :=
      Stacks.Chow.isGenericPoint_component_supp_of_relativeDimension_eq C f F k z hFk hzs hz
    exact Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp F Z z hZ
  · have : Subsingleton (F.presheaf.stalk z) :=
      not_nontrivial_iff_subsingleton.mp fun hn =>
        hzs ((SheafOfModules.mem_supp_iff_nontrivial_stalk F z).mpr hn)
    exact IsFiniteLength.of_subsingleton

/-! ### The multiplicity of an iterated `Tor` sheaf -/

/-- **The multiplicity of the left-associated iterated `Tor` sheaf at a point** is the length of
the left-associated iterated `Tor` module of the three stalks. -/
theorem sheafMultiplicity_iteratedTorSheafLeft (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ)
    (z : X) :
    Stacks.Chow.sheafMultiplicity (iteratedTorSheafLeft X F G H p q) z =
      (Module.length (X.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj (stalkModuleCat X F z)).obj
          (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X G z)).obj
            (stalkModuleCat X H z)))).toNat := by
  unfold Stacks.Chow.sheafMultiplicity
  congr 2
  exact (stalkIteratedTorLeftIso X F G H p q z).toLinearEquiv.length_eq

/-- **The multiplicity of the right-associated iterated `Tor` sheaf at a point** is the length of
the right-associated iterated `Tor` module of the three stalks. -/
theorem sheafMultiplicity_iteratedTorSheafRight (X : Scheme.{u}) (F G H : X.Modules) (p q : ℕ)
    (z : X) :
    Stacks.Chow.sheafMultiplicity (iteratedTorSheafRight X F G H p q) z =
      (Module.length (X.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj
            (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X F z)).obj
              (stalkModuleCat X G z))).obj (stalkModuleCat X H z))).toNat := by
  unfold Stacks.Chow.sheafMultiplicity
  congr 2
  exact (stalkIteratedTorRightIso X F G H p q z).toLinearEquiv.length_eq

/-- Above the dimension of `X` the left-associated iterated `Tor` module of the three stalks
vanishes. -/
theorem isZero_iteratedTorLeft_stalk (X : Scheme.{u})
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (F G H : X.Modules) (d p q : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdpq : d < p ∨ d < q) (z : X) :
    IsZero (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj (stalkModuleCat X F z)).obj
      (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X G z)).obj
        (stalkModuleCat X H z))) := by
  have : Subsingleton ((iteratedTorSheafLeft X F G H p q).presheaf.stalk z) :=
    not_nontrivial_iff_subsingleton.mp fun hn =>
      notMem_supp_iteratedTorSheafLeft_of_lt X hreg F G H d p q hd hdpq z
        ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ z).mpr hn)
  exact (ModuleCat.isZero_of_subsingleton
    (stalkModuleCat X (iteratedTorSheafLeft X F G H p q) z)).of_iso
      (stalkIteratedTorLeftIso X F G H p q z).symm

/-- Above the dimension of `X` the right-associated iterated `Tor` module of the three stalks
vanishes. -/
theorem isZero_iteratedTorRight_stalk (X : Scheme.{u})
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (F G H : X.Modules) (d p q : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdpq : d < p ∨ d < q) (z : X) :
    IsZero (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj
      (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X F z)).obj
        (stalkModuleCat X G z))).obj (stalkModuleCat X H z)) := by
  have : Subsingleton ((iteratedTorSheafRight X F G H p q).presheaf.stalk z) :=
    not_nontrivial_iff_subsingleton.mp fun hn =>
      notMem_supp_iteratedTorSheafRight_of_lt X hreg F G H d p q hd hdpq z
        ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ z).mpr hn)
  exact (ModuleCat.isZero_of_subsingleton
    (stalkModuleCat X (iteratedTorSheafRight X F G H p q) z)).of_iso
      (stalkIteratedTorRightIso X F G H p q z).symm

/-- At a point of delta-dimension `k` every left-associated iterated `Tor` module of the three
stalks has finite length. -/
theorem length_iteratedTorLeft_stalk_ne_top (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hL : IteratedTorSupportBoundLeft C f hX F G H hF hG hH k) (p q : ℕ) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k) :
    Module.length (X.presheaf.stalk z)
      (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj (stalkModuleCat X F z)).obj
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X G z)).obj
          (stalkModuleCat X H z))) ≠ ⊤ := by
  have := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH p q
  rw [← (stalkIteratedTorLeftIso X F G H p q z).toLinearEquiv.length_eq]
  exact length_stalk_ne_top_of_relativeDimension_eq C f (iteratedTorSheafLeft X F G H p q) k
    (hL p q) hz

/-- At a point of delta-dimension `k` every right-associated iterated `Tor` module of the three
stalks has finite length. -/
theorem length_iteratedTorRight_stalk_ne_top (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hR : IteratedTorSupportBoundRight C f hX F G H hF hG hH k) (p q : ℕ) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k) :
    Module.length (X.presheaf.stalk z)
      (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X F z)).obj
          (stalkModuleCat X G z))).obj (stalkModuleCat X H z)) ≠ ⊤ := by
  have := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH p q
  rw [← (stalkIteratedTorRightIso X F G H p q z).toLinearEquiv.length_eq]
  exact length_stalk_ne_top_of_relativeDimension_eq C f (iteratedTorSheafRight X F G H p q) k
    (hR p q) hz

/-! ### The coefficients of the two double sums -/

/-- Above the dimension of `X` a summand of the left-associated double sum is the zero cycle. -/
private lemma coherentSheafCycle_iteratedTorSheafLeft_eq_zero (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X)
    (F G H : X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hL : IteratedTorSupportBoundLeft C f hX F G H hF hG hH k) (d p q : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdpq : d < p ∨ d < q) :
    (haveI := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH p q
     Stacks.Chow.coherentSheafCycle C f (iteratedTorSheafLeft X F G H p q) k (hL p q)) = 0 := by
  have := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH p q
  exact coherentSheafCycle_eq_zero_of_relativeDimension_ne C f (iteratedTorSheafLeft X F G H p q) k
    (hL p q) (fun z hz => absurd hz (notMem_supp_iteratedTorSheafLeft_of_lt X
      (fun w => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX w) F G H d p q hd hdpq z))

/-- Above the dimension of `X` a summand of the right-associated double sum is the zero cycle. -/
private lemma coherentSheafCycle_iteratedTorSheafRight_eq_zero (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X)
    (F G H : X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hR : IteratedTorSupportBoundRight C f hX F G H hF hG hH k) (d p q : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdpq : d < p ∨ d < q) :
    (haveI := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH p q
     Stacks.Chow.coherentSheafCycle C f (iteratedTorSheafRight X F G H p q) k (hR p q)) = 0 := by
  have := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH p q
  exact coherentSheafCycle_eq_zero_of_relativeDimension_ne C f (iteratedTorSheafRight X F G H p q) k
    (hR p q) (fun z hz => absurd hz (notMem_supp_iteratedTorSheafRight_of_lt X
      (fun w => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX w) F G H d p q hd hdpq z))

/-- A function on `ℕ × ℕ` vanishing off the indices `p, q ≤ d` is supported in the finite box
`range (d + 2) ×ˢ range (d + 2)`. -/
private lemma support_subset_range_prod {M : Type*} [Zero M] (c : ℕ × ℕ → M) (d : ℕ)
    (h : ∀ p q : ℕ, d < p ∨ d < q → c (p, q) = 0) :
    Function.support c ⊆ ↑(Finset.range (d + 2) ×ˢ Finset.range (d + 2)) := by
  intro pq hpq
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  by_contra hn
  exact hpq (h pq.1 pq.2 (by omega))

/-- **The coefficient of the left-associated double sum at a point**, as a finite double sum of
the coefficients of the cycles of the iterated `Tor` sheaves. -/
theorem iteratedTorCycleLeft_apply (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hL : IteratedTorSupportBoundLeft C f hX F G H hF hG hH k) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (z : X) :
    iteratedTorCycleLeft C f hX F G H hF hG hH k hL z =
      ∑ pq ∈ Finset.range (d + 2) ×ˢ Finset.range (d + 2), ((-1 : ℤ) ^ (pq.1 + pq.2)) *
        (haveI := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH pq.1 pq.2
         Stacks.Chow.sheafCycleCoeff C f (iteratedTorSheafLeft X F G H pq.1 pq.2) k z) := by
  rw [iteratedTorCycleLeft, finsum_eq_sum_of_support_subset _
    (support_subset_range_prod _ d fun p q hdpq => ?_)]
  · simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Stacks.Chow.coherentSheafCycle]
    rfl
  · simp [coherentSheafCycle_iteratedTorSheafLeft_eq_zero C f hX F G H hF hG hH k hL d p q hd hdpq]

/-- **The coefficient of the right-associated double sum at a point**, as a finite double sum of
the coefficients of the cycles of the iterated `Tor` sheaves. -/
theorem iteratedTorCycleRight_apply (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G H : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hR : IteratedTorSupportBoundRight C f hX F G H hF hG hH k) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (z : X) :
    iteratedTorCycleRight C f hX F G H hF hG hH k hR z =
      ∑ pq ∈ Finset.range (d + 2) ×ˢ Finset.range (d + 2), ((-1 : ℤ) ^ (pq.1 + pq.2)) *
        (haveI := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH pq.1 pq.2
         Stacks.Chow.sheafCycleCoeff C f (iteratedTorSheafRight X F G H pq.1 pq.2) k z) := by
  rw [iteratedTorCycleRight, finsum_eq_sum_of_support_subset _
    (support_subset_range_prod _ d fun p q hdpq => ?_)]
  · simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Stacks.Chow.coherentSheafCycle]
    rfl
  · simp [coherentSheafCycle_iteratedTorSheafRight_eq_zero C f hX F G H hF hG hH k hR d p q hd hdpq]

/-! ### The two double sums as alternating sums of Section 43.14 products -/

/-- Regrouping a finitely supported alternating double sum over `ℕ × ℕ` as an alternating sum of
alternating sums, the inner one taken over the first index. -/
private lemma finsum_negOnePow_pow_smul_prod {M : Type*} [AddCommGroup M] (c : ℕ × ℕ → M)
    (hc : (Function.support c).Finite) :
    (∑ᶠ pq : ℕ × ℕ, ((-1 : ℤ) ^ (pq.1 + pq.2)) • c pq) =
      ∑ᶠ q : ℕ, ((-1 : ℤ) ^ q) • ∑ᶠ p : ℕ, ((-1 : ℤ) ^ p) • c (p, q) := by
  have hsub : ∀ (s : ℕ × ℕ → ℤ),
      (Function.support fun qp : ℕ × ℕ => s qp • c (qp.2, qp.1)) ⊆
        (fun qp : ℕ × ℕ => (qp.2, qp.1)) ⁻¹' Function.support c := by
    intro s qp hqp
    by_contra h
    simp only [Set.mem_preimage, Function.notMem_support] at h
    exact hqp (by simp [h])
  have hinj : ∀ t : Set (ℕ × ℕ), Set.InjOn (fun qp : ℕ × ℕ => (qp.2, qp.1)) t :=
    fun _ _ _ _ _ h => Prod.ext (Prod.ext_iff.1 h).2 (Prod.ext_iff.1 h).1
  have hswap : (Function.support fun qp : ℕ × ℕ =>
      ((-1 : ℤ) ^ qp.1) • (((-1 : ℤ) ^ qp.2) • c (qp.2, qp.1))).Finite := by
    refine (hc.preimage (hinj _)).subset ?_
    refine subset_trans (fun qp hqp => ?_) (hsub fun qp => (-1 : ℤ) ^ qp.1 * (-1 : ℤ) ^ qp.2)
    simpa only [Function.mem_support, mul_smul] using hqp
  have hinner : ∀ q : ℕ, (Function.support fun p : ℕ => ((-1 : ℤ) ^ p) • c (p, q)).Finite := by
    intro q
    refine (hc.preimage (f := fun p : ℕ => (p, q)) fun _ _ _ _ h => (Prod.ext_iff.1 h).1).subset ?_
    intro p hp
    by_contra h
    simp only [Set.mem_preimage, Function.notMem_support] at h
    exact hp (by simp [h])
  symm
  calc (∑ᶠ q : ℕ, ((-1 : ℤ) ^ q) • ∑ᶠ p : ℕ, ((-1 : ℤ) ^ p) • c (p, q))
      = ∑ᶠ q : ℕ, ∑ᶠ p : ℕ, ((-1 : ℤ) ^ q) • (((-1 : ℤ) ^ p) • c (p, q)) :=
        finsum_congr fun q => smul_finsum' _ (hinner q)
    _ = ∑ᶠ qp : ℕ × ℕ, ((-1 : ℤ) ^ qp.1) • (((-1 : ℤ) ^ qp.2) • c (qp.2, qp.1)) :=
        (finsum_curry _ hswap).symm
    _ = ∑ᶠ pq : ℕ × ℕ, ((-1 : ℤ) ^ (pq.1 + pq.2)) • c pq := by
        refine Eq.trans ?_ (finsum_comp_equiv (Equiv.prodComm ℕ ℕ)
          (f := fun pq : ℕ × ℕ => ((-1 : ℤ) ^ (pq.1 + pq.2)) • c pq))
        refine finsum_congr fun qp => ?_
        change ((-1 : ℤ) ^ qp.1) • (((-1 : ℤ) ^ qp.2) • c (qp.2, qp.1)) =
          ((-1 : ℤ) ^ (qp.2 + qp.1)) • c (qp.2, qp.1)
        rw [smul_smul, ← pow_add, add_comm]

/-- **The left-associated double sum as an alternating sum of Section 43.14 products.** Summing
the inner index first,

`∑ₚ_q (-1)^(p+q) [Torₚ(ℱ, Tor_q(𝒢, ℋ))]_k = ∑_q (-1)^q (ℱ · Tor_q(𝒢, ℋ))`,

where `ℱ · Tor_q(𝒢, ℋ) = ∑ₚ (-1)^p [Torₚ(ℱ, Tor_q(𝒢, ℋ))]_k` is the intersection product
`AlgebraicGeometry.TorFormula.intersectionProductCycle` of Section 43.14 of `ℱ` against the
`q`-th `Tor` sheaf of `𝒢` and `ℋ`. -/
theorem iteratedTorCycleLeft_eq_finsum_intersectionProductCycle
    (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (hX : IsRegular X) (F G H : X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent)
    (hH : H.IsCoherent) (k : ℤ) (hL : IteratedTorSupportBoundLeft C f hX F G H hF hG hH k)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    iteratedTorCycleLeft C f hX F G H hF hG hH k hL =
      ∑ᶠ q : ℕ, ((-1 : ℤ) ^ q) • intersectionProductCycle C f hX F (torSheaf X G H q) hF
        (isCoherent_torSheaf_of_isRegular X hX G H hG hH q) k (fun p => hL p q) := by
  have hfin : (Function.support fun pq : ℕ × ℕ =>
      have := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH pq.1 pq.2
      Stacks.Chow.coherentSheafCycle C f (iteratedTorSheafLeft X F G H pq.1 pq.2) k
        (hL pq.1 pq.2)).Finite := by
    exact (Finset.finite_toSet _).subset (support_subset_range_prod _ d fun p q hdpq =>
      coherentSheafCycle_iteratedTorSheafLeft_eq_zero C f hX F G H hF hG hH k hL d p q hd hdpq)
  rw [iteratedTorCycleLeft, finsum_negOnePow_pow_smul_prod _ hfin]
  exact finsum_congr fun q => rfl

/-- **The right-associated double sum as an alternating sum of Section 43.14 products.** -/
theorem iteratedTorCycleRight_eq_finsum_intersectionProductCycle
    (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (hX : IsRegular X) (F G H : X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent)
    (hH : H.IsCoherent) (k : ℤ) (hR : IteratedTorSupportBoundRight C f hX F G H hF hG hH k)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    iteratedTorCycleRight C f hX F G H hF hG hH k hR =
      ∑ᶠ q : ℕ, ((-1 : ℤ) ^ q) • intersectionProductCycle C f hX (torSheaf X F G q) H
        (isCoherent_torSheaf_of_isRegular X hX F G hF hG q) hH k (fun p => hR p q) := by
  have hfin : (Function.support fun pq : ℕ × ℕ =>
      have := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH pq.1 pq.2
      Stacks.Chow.coherentSheafCycle C f (iteratedTorSheafRight X F G H pq.1 pq.2) k
        (hR pq.1 pq.2)).Finite := by
    exact (Finset.finite_toSet _).subset (support_subset_range_prod _ d fun p q hdpq =>
      coherentSheafCycle_iteratedTorSheafRight_eq_zero C f hX F G H hF hG hH k hR d p q hd hdpq)
  rw [iteratedTorCycleRight, finsum_negOnePow_pow_smul_prod _ hfin]
  exact finsum_congr fun q => rfl

/-! ### The two double sums agree -/

/-- **Associativity of the triple intersection product, as an identity of cycles.** On a regular
scheme of dimension at most `d`, for coherent modules `ℱ`, `𝒢`, `ℋ` whose iterated `Tor` sheaves
have supports of delta-dimension at most `k`,

`∑ₚ_q (-1)^(p+q) [Torₚ(ℱ, Tor_q(𝒢, ℋ))]_k = ∑ₚ_q (-1)^(p+q) [Torₚ(Tor_q(ℱ, 𝒢), ℋ)]_k`

as cycles on `X`. The two sides are compared coefficient by coefficient: away from the points of
delta-dimension `k` both vanish, and at such a point each coefficient is the alternating double
sum of the lengths of the iterated `Tor` modules of the three stalks, which agree by
`Stacks.Intersection.finsum_alternating_length_tor_assoc`. -/
theorem iteratedTorCycleLeft_eq_iteratedTorCycleRight (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X)
    (F G H : X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent) (k : ℤ)
    (hL : IteratedTorSupportBoundLeft C f hX F G H hF hG hH k)
    (hR : IteratedTorSupportBoundRight C f hX F G H hF hG hH k) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    iteratedTorCycleLeft C f hX F G H hF hG hH k hL =
      iteratedTorCycleRight C f hX F G H hF hG hH k hR := by
  have hregz : ∀ w : X, IsRegularLocalRing (X.presheaf.stalk w) :=
    fun w => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX w
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [iteratedTorCycleLeft_apply C f hX F G H hF hG hH k hL d hd z,
    iteratedTorCycleRight_apply C f hX F G H hF hG hH k hR d hd z]
  by_cases hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k
  · have hcoeffL : ∀ p q : ℕ,
        (have := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH p q
         Stacks.Chow.sheafCycleCoeff C f (iteratedTorSheafLeft X F G H p q) k z) =
        ((Module.length (X.presheaf.stalk z)
          (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj (stalkModuleCat X F z)).obj
            (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X G z)).obj
              (stalkModuleCat X H z)))).toNat : ℤ) := by
      intro p q
      have := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH p q
      refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
        C f (iteratedTorSheafLeft X F G H p q) k (hL p q) hz) ?_
      exact sheafMultiplicity_iteratedTorSheafLeft X F G H p q z
    have hcoeffR : ∀ p q : ℕ,
        (have := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH p q
         Stacks.Chow.sheafCycleCoeff C f (iteratedTorSheafRight X F G H p q) k z) =
        ((Module.length (X.presheaf.stalk z)
          (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) p).obj
            (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) q).obj (stalkModuleCat X F z)).obj
              (stalkModuleCat X G z))).obj (stalkModuleCat X H z))).toNat : ℤ) := by
      intro p q
      have := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH p q
      refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
        C f (iteratedTorSheafRight X F G H p q) k (hR p q) hz) ?_
      exact sheafMultiplicity_iteratedTorSheafRight X F G H p q z
    refine Eq.trans (Finset.sum_congr rfl fun pq _ => by rw [hcoeffL pq.1 pq.2]) ?_
    refine Eq.trans ?_ (Finset.sum_congr rfl fun pq _ => by rw [hcoeffR pq.1 pq.2]).symm
    rw [← finsum_eq_sum_of_support_subset _ (support_subset_range_prod _ d fun p q hdpq => ?_),
      ← finsum_eq_sum_of_support_subset _ (support_subset_range_prod _ d fun p q hdpq => ?_)]
    rotate_left
    · simp [length_eq_zero_of_isZero (isZero_iteratedTorRight_stalk X hregz F G H d p q hd hdpq z)]
    · simp [length_eq_zero_of_isZero (isZero_iteratedTorLeft_stalk X hregz F G H d p q hd hdpq z)]
    exact Stacks.Intersection.finsum_alternating_length_tor_assoc (X.presheaf.stalk z)
      (stalkModuleCat X F z) (stalkModuleCat X G z) (stalkModuleCat X H z) d
      (fun p q => length_iteratedTorLeft_stalk_ne_top C f hX F G H hF hG hH k hL p q hz)
      (fun p q => length_iteratedTorRight_stalk_ne_top C f hX F G H hF hG hH k hR p q hz)
      (fun p q h => isZero_iteratedTorLeft_stalk X hregz F G H d p q hd h z)
      (fun p q h => isZero_iteratedTorRight_stalk X hregz F G H d p q hd h z)
  · refine Eq.trans (Finset.sum_eq_zero fun pq _ => ?_)
      (Finset.sum_eq_zero fun pq _ => ?_).symm
    · have := isCoherent_iteratedTorSheafLeft X hX F G H hF hG hH pq.1 pq.2
      simp [Stacks.Chow.sheafCycleCoeff, hz]
    · have := isCoherent_iteratedTorSheafRight X hX F G H hF hG hH pq.1 pq.2
      simp [Stacks.Chow.sheafCycleCoeff, hz]

/-! ### The three closed subvarieties of Section 43.20 -/

/-- **The bound of Section 43.20 discharged, left-associated.** If the triple intersection of the
reduced closures of three points has dimension at most `m`, then every left-associated iterated
`Tor` sheaf of their structure sheaves has support of delta-dimension at most `m`, which is what
makes the alternating double sum a sum of `m`-cycles. -/
theorem iteratedTorSupportBoundLeft_of_topologicalKrullDim_le (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (u v w : X) (m : ℕ)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) ≤
      (m : WithBot ℕ∞)) :
    IteratedTorSupportBoundLeft (Stacks.Chow.fieldChowSituation k) sX hX
      (structureSheafAt u) (structureSheafAt v) (structureSheafAt w)
      (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
      (isCoherent_structureSheafAt w) (m : ℤ) := by
  intro p q
  have := isCoherent_iteratedTorSheafLeft X hX (structureSheafAt u) (structureSheafAt v)
    (structureSheafAt w) (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
    (isCoherent_structureSheafAt w) p q
  refine Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k sX _ m ?_
  refine le_trans ?_ huvw
  refine (Topology.IsEmbedding.inclusion ?_).isInducing.topologicalKrullDim_le
  refine (supp_iteratedTorSheafLeft_subset X (structureSheafAt u) (structureSheafAt v)
    (structureSheafAt w) p q).trans ?_
  rw [supp_structureSheafAt, supp_structureSheafAt, supp_structureSheafAt]

/-- **The bound of Section 43.20 discharged, right-associated.** -/
theorem iteratedTorSupportBoundRight_of_topologicalKrullDim_le (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (u v w : X) (m : ℕ)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) ≤
      (m : WithBot ℕ∞)) :
    IteratedTorSupportBoundRight (Stacks.Chow.fieldChowSituation k) sX hX
      (structureSheafAt u) (structureSheafAt v) (structureSheafAt w)
      (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
      (isCoherent_structureSheafAt w) (m : ℤ) := by
  intro p q
  have := isCoherent_iteratedTorSheafRight X hX (structureSheafAt u) (structureSheafAt v)
    (structureSheafAt w) (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
    (isCoherent_structureSheafAt w) p q
  refine Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k sX _ m ?_
  refine le_trans ?_ huvw
  refine (Topology.IsEmbedding.inclusion ?_).isInducing.topologicalKrullDim_le
  refine (supp_iteratedTorSheafRight_subset X (structureSheafAt u) (structureSheafAt v)
    (structureSheafAt w) p q).trans ?_
  rw [supp_structureSheafAt, supp_structureSheafAt, supp_structureSheafAt]

/-- **Stacks 0B1L, as an identity of cycles on `X`.** Let `X` be a nonsingular variety over `k`
of dimension at most `n`, and let `U`, `V`, `W` be the reduced closures of three points, with
`dim (U ∩ V ∩ W) ≤ m`. Then the two alternating double sums of Section 43.20,

`∑ᵢⱼ (-1)ⁱ⁺ʲ [Torᵢ(𝒪_U, Torⱼ(𝒪_V, 𝒪_W))]_m`  and  `∑ᵢⱼ (-1)ⁱ⁺ʲ [Torᵢ(Torⱼ(𝒪_U, 𝒪_V), 𝒪_W)]_m`,

agree as cycles on `X`. In the source's notation `m = dim U + dim V + dim W - 2 dim X`, and the
hypothesis `dim (U ∩ V ∩ W) ≤ m` is the displayed dimension hypothesis of the lemma; the
delta-dimension bounds that make the two sums sums of `m`-cycles are discharged from it. -/
theorem iteratedTorCycle_assoc_of_closures (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (u v w : X) (n m : ℕ)
    (hdimX : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) ≤
      (m : WithBot ℕ∞)) :
    iteratedTorCycleLeft (Stacks.Chow.fieldChowSituation k) sX hX
        (structureSheafAt u) (structureSheafAt v) (structureSheafAt w)
        (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
        (isCoherent_structureSheafAt w) (m : ℤ)
        (iteratedTorSupportBoundLeft_of_topologicalKrullDim_le k sX hX u v w m huvw) =
      iteratedTorCycleRight (Stacks.Chow.fieldChowSituation k) sX hX
        (structureSheafAt u) (structureSheafAt v) (structureSheafAt w)
        (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
        (isCoherent_structureSheafAt w) (m : ℤ)
        (iteratedTorSupportBoundRight_of_topologicalKrullDim_le k sX hX u v w m huvw) :=
  iteratedTorCycleLeft_eq_iteratedTorCycleRight (Stacks.Chow.fieldChowSituation k) sX hX
    (structureSheafAt u) (structureSheafAt v) (structureSheafAt w)
    (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
    (isCoherent_structureSheafAt w) (m : ℤ) _ _ n hdimX

/-- **Stacks 0B1L, as an identity of Section 43.14 intersection products on `X`.** Let `X` be a
nonsingular variety over `k` of dimension at most `n`, and let `U`, `V`, `W` be the reduced
closures of three points, with `dim (U ∩ V ∩ W) ≤ m`. Then

`∑ᵢ (-1)ⁱ (U · Torᵢ(𝒪_V, 𝒪_W)) = ∑ᵢ (-1)ⁱ (Torᵢ(𝒪_U, 𝒪_V) · W)`

as cycles on `X`, each summand being the intersection product
`AlgebraicGeometry.TorFormula.intersectionProductCycle` of Section 43.14 of a structure sheaf
against a `Tor` sheaf. These are the two displays the source's proof of the lemma computes
`U · (V · W)` and `(U · V) · W` to be, with `m = dim U + dim V + dim W - 2 dim X`.

No `@[stacks 0B1L]` attribute.  Stacks 0B1L is the cycle identity
`U · (V · W) = (U · V) · W`; what is proved here is the regrouping of each side into an
alternating sum of Section 43.14 intersection products.  Identifying those sums with the triple
products is Stacks 0B0W's Tor formula at the cycle level, and that step is taken elsewhere:
the tag is carried by
`Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_assoc` in
`StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.SubvarietyProductAssociativity`,
whose main case
`Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_assoc_of_closures`
feeds this identity to `Stacks.Intersection.ReductionToDiagonal.torFormula`.  Registering
the tag here would put it on an intermediate identity, which this development does not do. -/
theorem intersectionProductCycle_assoc_of_closures (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (u v w : X) (n m : ℕ)
    (hdimX : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) ≤
      (m : WithBot ℕ∞)) :
    (∑ᶠ q : ℕ, ((-1 : ℤ) ^ q) •
        intersectionProductCycle (Stacks.Chow.fieldChowSituation k) sX hX (structureSheafAt u)
          (torSheaf X (structureSheafAt v) (structureSheafAt w) q)
          (isCoherent_structureSheafAt u)
          (isCoherent_torSheaf_of_isRegular X hX (structureSheafAt v) (structureSheafAt w)
            (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) q) (m : ℤ)
          (fun p =>
            iteratedTorSupportBoundLeft_of_topologicalKrullDim_le k sX hX u v w m huvw p q)) =
      ∑ᶠ q : ℕ, ((-1 : ℤ) ^ q) •
        intersectionProductCycle (Stacks.Chow.fieldChowSituation k) sX hX
          (torSheaf X (structureSheafAt u) (structureSheafAt v) q) (structureSheafAt w)
          (isCoherent_torSheaf_of_isRegular X hX (structureSheafAt u) (structureSheafAt v)
            (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v) q)
          (isCoherent_structureSheafAt w) (m : ℤ)
          (fun p =>
            iteratedTorSupportBoundRight_of_topologicalKrullDim_le k sX hX u v w m huvw p q) :=
  Eq.trans
    (iteratedTorCycleLeft_eq_finsum_intersectionProductCycle (Stacks.Chow.fieldChowSituation k)
      sX hX (structureSheafAt u) (structureSheafAt v) (structureSheafAt w)
      (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
      (isCoherent_structureSheafAt w) (m : ℤ)
      (iteratedTorSupportBoundLeft_of_topologicalKrullDim_le k sX hX u v w m huvw) n hdimX).symm
    (Eq.trans (iteratedTorCycle_assoc_of_closures k sX hX u v w n m hdimX huvw)
      (iteratedTorCycleRight_eq_finsum_intersectionProductCycle
        (Stacks.Chow.fieldChowSituation k) sX hX (structureSheafAt u) (structureSheafAt v)
        (structureSheafAt w) (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
        (isCoherent_structureSheafAt w) (m : ℤ)
        (iteratedTorSupportBoundRight_of_topologicalKrullDim_le k sX hX u v w m huvw) n hdimX))

end AlgebraicGeometry.TorFormula

end
