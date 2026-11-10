module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionProjection
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BivariantDivision
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FEF (2) as an equality of bivariant classes

Let `π : E = Proj_X(Sym^*(𝒞)[T]) ⟶ X` be the projective completion of a locally free module of
rank `r`, `i : X ⟶ E` its zero section, and `j : C ⟶ E`, `p : C ⟶ X` the inclusion and the
structure morphism of the vector bundle `C = Spec_X(Sym^*(𝒞))`. For every `s : X ⟶ X₀` and every
bivariant class `c ∈ A^q(E ⟶ X₀)`,

  `p^* ∘ π_* ∘ (c_r(i_*𝒪_X) ∘ c) = (-1)^{r-1} (r-1)! (j^* ∘ c)`  in `A^q(C ⟶ X₀)`,

the identity `p^* ∘ π_* ∘ c_r(i_*𝒪_X) = (-1)^{r-1} (r-1)! j^*` of Stacks 0FEF composed with a
class on its right. The caps of both sides on a test scheme `t : T ⟶ X₀` are computed on the base
change `E ×_{X₀} T = E ×_X (X ×_{X₀} T)`, where the identity is the cartesian-square form of the
second conclusion proved in
`StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionProjection`; the rest is
the identification of the fibre products the composites of Stacks 0B75 and the pushforward of
Stacks 0EPK produce.

## Main results

* `Stacks.Chow.ProjectiveCompletion.bivariantClass_zeroSecObject`: Stacks 0FEF (2) as an equality
  of bivariant classes.
* `Stacks.Chow.ProjectiveCompletion.properChowPushforward_flatPullbackChow_comp_of_isIso`:
  pushing forward along an isomorphism `ψ` turns flat pullback along `ψ ≫ m` into flat pullback
  along `m`.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.ProjectiveCompletion

/-! ### Transports along isomorphisms and equalities -/

section Transport

variable (C : ChowSituation.{u})

/-- Integer multiples of heterogeneously equal elements, for equal structure morphisms and equal
degrees. -/
theorem chowGroup_zsmul_heq_of_structure {Y : Scheme.{u}} {q q' : Y ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') {d d' : ℤ} (hd : d = d')
    {x : chowGroup C q d} {y : chowGroup C q' d'} (hxy : x ≍ y) (n : ℤ) : n • x ≍ n • y := by
  subst hq hd
  cases hxy
  rfl

/-- Relative dimension along equal morphisms. -/
theorem relativeDimension_of_eq {A B : Scheme.{u}} {m m' : A ⟶ B} [LocallyOfFiniteType m]
    [LocallyOfFiniteType m'] (h : m = m') {d : ℕ} (hd : AlgebraicGeometry.RelativeDimension m d) :
    AlgebraicGeometry.RelativeDimension m' d := by
  subst h
  exact hd

/-- Flat pullback along equal morphisms, read on equal structure morphisms. -/
theorem flatPullbackChow_heq_of_eq {A B : Scheme.{u}} {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA]
    [LocallyOfFiniteType sA'] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] {m m' : A ⟶ B}
    [LocallyOfFiniteType m] [Flat m] [LocallyOfFiniteType m'] [Flat m'] (hs : sA = sA')
    (hm : m = m') (hb : m ≫ sB = sA) (hb' : m' ≫ sB = sA') {d d' : ℕ} (hd : d = d')
    (hr : AlgebraicGeometry.RelativeDimension m d)
    (hr' : AlgebraicGeometry.RelativeDimension m' d') (k : ℤ) (x : chowGroup C sB k) :
    flatPullbackChow C sA sB m hb d hr k
        (flatPullbackFactorsThroughRationalEquivalence_general C sA sB m hb d hr k) x ≍
      flatPullbackChow C sA' sB m' hb' d' hr' k
        (flatPullbackFactorsThroughRationalEquivalence_general C sA' sB m' hb' d' hr' k) x := by
  subst hs hm hd
  rfl

/-- Proper pushforward along equal morphisms, read on equal structure morphisms and degrees. -/
theorem properChowPushforward_heq_of_eq {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {m m' : A ⟶ B} [IsProper m] [IsProper m'] (hs : sA = sA') (hm : m = m')
    (hb : m ≫ sB = sA) (hb' : m' ≫ sB = sA') {k k' : ℤ} (hk : k = k')
    {x : chowGroup C sA k} {x' : chowGroup C sA' k'} (hx : x ≍ x') :
    properChowPushforward C sA sB m hb k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sA sB m hb k) x ≍
      properChowPushforward C sA' sB m' hb' k'
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sA' sB m' hb' k') x' := by
  subst hs hm hk
  cases hx
  rfl

/-- **Pushing forward along an isomorphism undoes flat pullback along it.** -/
theorem properChowPushforward_flatPullbackChow_of_isIso {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (ψ : A ⟶ B) [IsIso ψ]
    (hψ : ψ ≫ sB = sA) (k : ℤ) (y : chowGroup C sB k) :
    properChowPushforward C sA sB ψ hψ (k + ((0 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sA sB ψ hψ _)
        (flatPullbackChow C sA sB ψ hψ 0 (relativeDimension_of_isIso ψ) k
          (flatPullbackFactorsThroughRationalEquivalence_general C sA sB ψ hψ 0
            (relativeDimension_of_isIso ψ) k) y) ≍ y := by
  have hinv : inv ψ ≫ sA = sB := by rw [← hψ, IsIso.inv_hom_id_assoc]
  have h1 := flatPullbackChowOfRelativeDimension_of_isIso C sA sB ψ hψ
    (relativeDimension_of_isIso ψ) (inv ψ) (IsIso.inv_hom_id ψ) hinv k y
  change properChowPushforward C sA sB ψ hψ _ _ (flatPullbackChowOfRelativeDimension C sA sB ψ hψ
    0 (relativeDimension_of_isIso ψ) k y) ≍ y
  rw [h1]
  refine (properChowPushforward_heq C sA sB ψ hψ (by simp) (chowGroupCast_heq C _ _ _)).trans ?_
  have h2 := DFunLike.congr_fun (properChowPushforward_comp C sB sA sB (inv ψ) ψ hinv hψ k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)) y
  refine (heq_of_eq h2).trans ?_
  exact heq_of_eq ((properChowPushforward_congr_hom C sB sB (IsIso.inv_hom_id ψ) _
    (Category.id_comp sB) k _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB sB (𝟙 B)
      (Category.id_comp sB) k) y).trans (chowPushforwardOfIso_id C sB k y))

/-- **Pushforward along an isomorphism of a flat pullback.** If `m_A = ψ ≫ m_B` with `ψ` an
isomorphism, then `ψ_* m_A^* = m_B^*`. -/
theorem properChowPushforward_flatPullbackChow_comp_of_isIso {A B Z : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (ψ : A ⟶ B) [IsIso ψ] (hψ : ψ ≫ sB = sA)
    (mA : A ⟶ Z) (mB : B ⟶ Z) [LocallyOfFiniteType mA] [Flat mA] [LocallyOfFiniteType mB]
    [Flat mB] (hm : ψ ≫ mB = mA) (hA : mA ≫ sZ = sA) (hB : mB ≫ sZ = sB) (d : ℕ)
    (hdA : AlgebraicGeometry.RelativeDimension mA d)
    (hdB : AlgebraicGeometry.RelativeDimension mB d) (k : ℤ) (y : chowGroup C sZ k) :
    properChowPushforward C sA sB ψ hψ (k + d)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sA sB ψ hψ _)
        (flatPullbackChow C sA sZ mA hA d hdA k
          (flatPullbackFactorsThroughRationalEquivalence_general C sA sZ mA hA d hdA k) y) =
      flatPullbackChow C sB sZ mB hB d hdB k
        (flatPullbackFactorsThroughRationalEquivalence_general C sB sZ mB hB d hdB k) y := by
  have hc := flatPullbackChow_comp C sA sB sZ ψ mB hψ hB 0 d (relativeDimension_of_isIso ψ) hdB k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) y
  exact eq_of_heq ((properChowPushforward_heq C sA sB ψ hψ (by push_cast; ring)
    ((flatPullbackChow_heq_of_eq C sZ rfl hm.symm hA _ (Nat.zero_add d).symm hdA _ k y).trans
      hc.symm)).trans (properChowPushforward_flatPullbackChow_of_isIso C sA sB ψ hψ _ _))

/-- **The cap of a class read for an equal morphism**: the cap of the original class, pushed
forward along the identification of the two fibre products. -/
theorem copy_cap_heq (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f f' : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff' : f = f') (hf : f ≫ sY = sX)
    (hf' : f' ≫ sY = sX) {p p' : ℤ} (hpp' : p = p') (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (BivariantClass.copy C G sX sY hff' hf hf' hpp' c).cap g k α ≍
      properChowPushforward C (pullback.fst f g ≫ sX) (pullback.fst f' g ≫ sX)
        (pullback.map f g f' g (𝟙 X) (𝟙 T) (𝟙 Y) (by simp [hff']) (by simp))
        (by simp) (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)
        (c.cap g k α) := by
  subst hff' hpp'
  refine (BivariantClass.copy_cap C G sX sY rfl hf hf' rfl c g k α).trans ?_
  refine HEq.symm (heq_of_eq ?_)
  exact (properChowPushforward_congr_hom C _ _ pullback.map_id _ (Category.id_comp _) _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ (𝟙 _)
      (Category.id_comp _) _) _).trans (chowPushforwardOfIso_id C _ _ _)

end Transport

/-! ### The two bivariant classes -/

section Classes

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)]
  {X₀ : Scheme.{u}} (sX₀ : X₀ ⟶ C.S) [LocallyOfFiniteType sX₀] (s : X ⟶ X₀)
  [LocallyOfFiniteType s] (hs : s ≫ sX₀ = sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] in
/-- The inclusion `j : C ⟶ E` is a morphism over the base. -/
theorem vectorBundleIncl_comp_structure :
    vectorBundleIncl 𝒞 r ≫ proj 𝒞 ≫ sX = Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX := by
  rw [← Category.assoc, vectorBundleIncl_proj]

/-- `c_r(i_*𝒪_X) ∈ A^r(E)`. -/
abbrev chernTopClass :
    chowCohomologyComponent C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) (r : ℤ) :=
  perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r) r

/-- The flat pullback class `p^* ∈ A^{-r}(C ⟶ X)` of the vector bundle. -/
abbrev vectorBundleFlatClass :
    BivariantClass C (gysinSystemOfInvertible C) (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX) sX
      (Scheme.Modules.vectorBundleToBase X 𝒞) rfl (-(r : ℤ)) :=
  flatPullbackBivariantClassOfInvertible C _ sX _ rfl r
    (relativeDimension_vectorBundleToBase 𝒞 r)

/-- The flat pullback class `j^* ∈ A^0(C ⟶ E)` of the open immersion `j`. -/
abbrev inclFlatClass :
    BivariantClass C (gysinSystemOfInvertible C) (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX)
      (proj 𝒞 ≫ sX) (vectorBundleIncl 𝒞 r) (vectorBundleIncl_comp_structure 𝒞 r C sX)
      (-((0 : ℕ) : ℤ)) :=
  flatPullbackBivariantClassOfInvertible C _ _ _ (vectorBundleIncl_comp_structure 𝒞 r C sX) 0
    (relativeDimension_of_isOpenImmersion _)

/-- **`p^* ∘ π_* ∘ (c_r(i_*𝒪_X) ∘ c)`** for `c ∈ A^q(E ⟶ X₀)`: the composite with `c` of
`c_r(i_*𝒪_X) ∈ A^r(E)` (Stacks 0B75), pushed forward along `π` (Stacks 0EPK), composed with the
flat pullback class `p^*` (Stacks 0B78, 0B75). -/
def lhsClass {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
    (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q) :
    BivariantClass C (gysinSystemOfInvertible C) (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX) sX₀
      (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs)
      (-(r : ℤ) + ((r : ℤ) + q)) :=
  bivariantCompositeOfInvertible C _ sX sX₀ _ s rfl hs (-(r : ℤ)) ((r : ℤ) + q)
    (vectorBundleFlatClass 𝒞 r C sX)
    (canonicalBivariantProperPushforward C (proj 𝒞 ≫ sX) sX sX₀ (proj 𝒞) s rfl hs ((r : ℤ) + q)
      (BivariantClass.copy C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
        (Category.id_comp (proj 𝒞 ≫ s)) _ _ rfl
        (bivariantCompositeOfInvertible C (proj 𝒞 ≫ sX) (proj 𝒞 ≫ sX) sX₀ (𝟙 _) (proj 𝒞 ≫ s)
          (Category.id_comp _) (comp_comp_structureMorphism_eq rfl hs) (r : ℤ) q
          (chernTopClass 𝒞 r C sX) c)))

/-- **`j^* ∘ c`** for `c ∈ A^q(E ⟶ X₀)`. -/
def rhsClass {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
    (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q) :
    BivariantClass C (gysinSystemOfInvertible C) (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX) sX₀
      (vectorBundleIncl 𝒞 r ≫ proj 𝒞 ≫ s)
      (comp_comp_structureMorphism_eq (vectorBundleIncl_comp_structure 𝒞 r C sX)
        (comp_comp_structureMorphism_eq rfl hs)) (-((0 : ℕ) : ℤ) + q) :=
  bivariantCompositeOfInvertible C _ (proj 𝒞 ≫ sX) sX₀ (vectorBundleIncl 𝒞 r) (proj 𝒞 ≫ s)
    (vectorBundleIncl_comp_structure 𝒞 r C sX) (comp_comp_structureMorphism_eq rfl hs)
    (-((0 : ℕ) : ℤ)) q (inclFlatClass 𝒞 r C sX) c

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- `j ≫ π ≫ s = p ≫ s`: the inclusion `j : C ⟶ E` is a morphism over `X₀`. -/
theorem incl_proj_comp :
    vectorBundleIncl 𝒞 r ≫ proj 𝒞 ≫ s = Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s := by
  rw [← Category.assoc, vectorBundleIncl_proj]

section Squares

variable {T : Scheme.{u}} (t : T ⟶ X₀)

/-- The map `C ×_{X₀} T ⟶ E ×_{X₀} T` induced by `j`. -/
def inclBase :
    pullback (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t ⟶ pullback (proj 𝒞 ≫ s) t :=
  pullback.lift (pullback.fst _ t ≫ vectorBundleIncl 𝒞 r) (pullback.snd _ t)
    (by rw [Category.assoc, incl_proj_comp 𝒞 r s, pullback.condition])

/-- The map `C ×_{X₀} T ⟶ X ×_{X₀} T` induced by `p`. -/
def projBase :
    pullback (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t ⟶ pullback s t :=
  pullback.lift (pullback.fst _ t ≫ Scheme.Modules.vectorBundleToBase X 𝒞) (pullback.snd _ t)
    (by rw [Category.assoc, pullback.condition])

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The first projection of `C ×_{X₀} T ⟶ E ×_{X₀} T` is `j` on the first factor. -/
theorem inclBase_fst :
    inclBase 𝒞 r s t ≫ pullback.fst (proj 𝒞 ≫ s) t =
      pullback.fst (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t ≫ vectorBundleIncl 𝒞 r :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The map `C ×_{X₀} T ⟶ E ×_{X₀} T` commutes with the projections to `T`. -/
theorem inclBase_snd :
    inclBase 𝒞 r s t ≫ pullback.snd (proj 𝒞 ≫ s) t =
      pullback.snd (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t :=
  pullback.lift_snd _ _ _

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The first projection of `C ×_{X₀} T ⟶ X ×_{X₀} T` is `p` on the first factor. -/
theorem projBase_fst :
    projBase 𝒞 s t ≫ pullback.fst s t =
      pullback.fst (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t ≫
        Scheme.Modules.vectorBundleToBase X 𝒞 :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The map `C ×_{X₀} T ⟶ X ×_{X₀} T` commutes with the projections to `T`. -/
theorem projBase_snd :
    projBase 𝒞 s t ≫ pullback.snd s t =
      pullback.snd (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t :=
  pullback.lift_snd _ _ _

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The map `C ×_{X₀} T ⟶ X ×_{X₀} T` induced by `p` is the one induced by `j` followed by the
base change of `π`. -/
theorem inclBase_comp :
    inclBase 𝒞 r s t ≫ bivariantPushforwardBaseChange (proj 𝒞) s t = projBase 𝒞 s t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc, inclBase_fst,
      projBase_fst, Category.assoc, vectorBundleIncl_proj]
  · rw [Category.assoc, bivariantPushforwardBaseChange_snd, inclBase_snd, projBase_snd]

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The square formed by `j : C ⟶ E` and its base change `C ×_{X₀} T ⟶ E ×_{X₀} T` is
cartesian. -/
theorem isPullback_inclBase :
    IsPullback (pullback.fst (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t) (inclBase 𝒞 r s t)
      (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞 ≫ s) t) := by
  refine IsPullback.of_bot ?_ (inclBase_fst 𝒞 r s t).symm
    (IsPullback.of_hasPullback (proj 𝒞 ≫ s) t)
  rw [inclBase_snd, incl_proj_comp 𝒞 r s]
  exact IsPullback.of_hasPullback _ _

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- Under the identification `C ×_X (X ×_{X₀} T) ≅ C ×_{X₀} T`, the map `projBase` is the second
projection. -/
theorem pullbackRightPullbackFstIso_hom_projBase :
    (pullbackRightPullbackFstIso s t (Scheme.Modules.vectorBundleToBase X 𝒞)).hom ≫
        projBase 𝒞 s t =
      pullback.snd (Scheme.Modules.vectorBundleToBase X 𝒞) (pullback.fst s t) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projBase_fst, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  · rw [Category.assoc, projBase_snd, pullbackRightPullbackFstIso_hom_snd]

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- Under the identification `C ×_E (E ×_{X₀} T) ≅ C ×_{X₀} T`, the map `inclBase` is the second
projection. -/
theorem pullbackRightPullbackFstIso_hom_map_inclBase :
    ((pullbackRightPullbackFstIso (proj 𝒞 ≫ s) t (vectorBundleIncl 𝒞 r)).hom ≫
        pullback.map (vectorBundleIncl 𝒞 r ≫ proj 𝒞 ≫ s) t
          (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t (𝟙 _) (𝟙 T) (𝟙 X₀)
          (by simp [incl_proj_comp 𝒞 r s]) (by simp)) ≫ inclBase 𝒞 r s t =
      pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞 ≫ s) t) := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, inclBase_fst, pullback.map_fst_assoc, Category.id_comp,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    exact pullback.condition
  · simp only [Category.assoc, inclBase_snd, pullback.map_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd]

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The identification `E ×_E (E ×_{X₀} T) ≅ E ×_{X₀} T` is the second projection. -/
theorem pullbackRightPullbackFstIso_hom_map_id :
    (pullbackRightPullbackFstIso (proj 𝒞 ≫ s) t (𝟙 (space 𝒞))).hom ≫
        pullback.map (𝟙 _ ≫ proj 𝒞 ≫ s) t (proj 𝒞 ≫ s) t (𝟙 _) (𝟙 T) (𝟙 X₀)
          (by simp) (by simp) =
      pullback.snd (𝟙 (space 𝒞)) (pullback.fst (proj 𝒞 ≫ s) t) := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.map_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst]
    simpa only [Category.comp_id] using
      (pullback.condition (f := 𝟙 (space 𝒞)) (g := pullback.fst (proj 𝒞 ≫ s) t))
  · simp only [Category.assoc, pullback.map_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd]

end Squares

omit [Flat (proj 𝒞)] [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] in
/-- **The cap of `c_r(i_*𝒪_X) ∘ c`** is the operation of `c_r(i_*𝒪_X)` on the cap of `c`. -/
theorem copy_comp_chernTopClass_cap_heq {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C)
    (proj 𝒞 ≫ sX) sX₀ (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q) {T : Scheme.{u}}
    (t : T ⟶ X₀) [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C (t ≫ sX₀) k) :
    (BivariantClass.copy C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
        (Category.id_comp (proj 𝒞 ≫ s)) _ (comp_comp_structureMorphism_eq rfl hs) rfl
        (bivariantCompositeOfInvertible C (proj 𝒞 ≫ sX) (proj 𝒞 ≫ sX) sX₀ (𝟙 _) (proj 𝒞 ≫ s)
          (Category.id_comp _) (comp_comp_structureMorphism_eq rfl hs) (r : ℤ) q
          (chernTopClass 𝒞 r C sX) c)).cap t k β ≍
      (perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
        (pullback.fst (proj 𝒞 ≫ s) t) (k - q) r (c.cap t k β) := by
  refine (copy_cap_heq C _ _ _ (Category.id_comp _) _ _ rfl _ t k β).trans ?_
  refine (properChowPushforward_heq C _ _ _ _ (show k - ((r : ℤ) + q) = k - q - r by ring)
    (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_
  rw [bivariantCompositeCap_apply, ← AddMonoidHom.comp_apply, properChowPushforward_comp]
  refine (properChowPushforward_heq_of_eq C _ rfl
    (pullbackRightPullbackFstIso_hom_map_id 𝒞 s t) _
    (by rw [← Category.assoc, ← pullback.condition, Category.comp_id]) rfl HEq.rfl).trans ?_
  rw [TotalChowClass.op_apply, BivariantClass.idRule_apply]
  rfl

/-- The base change `C ×_{X₀} T ⟶ E ×_{X₀} T` of `j` is an open immersion. -/
instance isOpenImmersion_inclBase {T : Scheme.{u}} (t : T ⟶ X₀) :
    IsOpenImmersion (inclBase 𝒞 r s t) :=
  MorphismProperty.of_isPullback (isPullback_inclBase 𝒞 r s t) inferInstance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X 𝒞)]
  [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] [LocallyOfFiniteType s] in
/-- The map `C ×_{X₀} T ⟶ E ×_{X₀} T` is a morphism over `X`, after structure maps to the base. -/
private theorem inclBase_comp_structure {T : Scheme.{u}} (t : T ⟶ X₀) :
    inclBase 𝒞 r s t ≫ pullback.fst (proj 𝒞 ≫ s) t ≫ proj 𝒞 ≫ sX =
      pullback.fst (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t ≫
        Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX := by
  rw [← Category.assoc, inclBase_fst, Category.assoc, vectorBundleIncl_comp_structure]

/-- The cap of `lhsClass` on `t : T ⟶ X₀` is `(-1)^{r-1} (r-1)!` times the flat pullback along
`C ×_{X₀} T ⟶ E ×_{X₀} T` of the cap of `c`. -/
theorem lhsClass_cap_heq {q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
    (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q) {T : Scheme.{u}} (t : T ⟶ X₀)
    [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C (t ≫ sX₀) k) :
    (lhsClass 𝒞 r C sX sX₀ s hs c).cap t k β ≍
      ((((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
      flatPullbackChow C (inclBase 𝒞 r s t ≫ pullback.fst (proj 𝒞 ≫ s) t ≫ proj 𝒞 ≫ sX)
        (pullback.fst (proj 𝒞 ≫ s) t ≫ proj 𝒞 ≫ sX) (inclBase 𝒞 r s t) rfl 0
        (relativeDimension_of_isOpenImmersion _) (k - q)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
          (relativeDimension_of_isOpenImmersion _) (k - q)) (c.cap t k β))) := by
  have hsq := isPullback_bivariantPushforwardBaseChange (proj 𝒞) s t
  have : LocallyOfFiniteType (bivariantPushforwardBaseChange (proj 𝒞) s t) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have : Flat (bivariantPushforwardBaseChange (proj 𝒞) s t) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have : IsProper (bivariantPushforwardBaseChange (proj 𝒞) s t) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have hL := flatPullbackChow_properChowPushforward_perfectChernClass_of_isPullback 𝒞 r C sX hsq
    (inclBase 𝒞 r s t) (isPullback_inclBase 𝒞 r s t) (k - q) (c.cap t k β)
  have hjF := inclBase_comp_structure 𝒞 r C sX s t
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (properChowPushforward_heq C _ _
    (pullbackRightPullbackFstIso s t (Scheme.Modules.vectorBundleToBase X 𝒞)).hom _
    (show k - ((r : ℤ) + q) - -(r : ℤ) = k - q - r + r by ring)
    ((chowGroupDegreeEquiv_heq C _ _ _).trans
      (flatPullbackChow_heq C _ _ _ _ r _
        (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ r _ d)
        (show k - ((r : ℤ) + q) = k - q - r by ring)
        (properChowPushforward_heq C _ _ (bivariantPushforwardBaseChange (proj 𝒞) s t) _
          (show k - ((r : ℤ) + q) = k - q - r by ring)
          (copy_comp_chernTopClass_cap_heq 𝒞 r C sX sX₀ s hs c t k β))))).trans ?_
  have : LocallyOfFiniteType (projBase 𝒞 s t) := by
    rw [← inclBase_comp 𝒞 r s t]
    infer_instance
  have : Flat (projBase 𝒞 s t) := by
    rw [← inclBase_comp 𝒞 r s t]
    infer_instance
  have hdF : AlgebraicGeometry.RelativeDimension (projBase 𝒞 s t) r :=
    relativeDimension_of_eq (inclBase_comp 𝒞 r s t)
      (relativeDimension_incl_snd 𝒞 r hsq (inclBase 𝒞 r s t))
  have hB : projBase 𝒞 s t ≫ pullback.fst s t ≫ sX =
      pullback.fst (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t ≫
        Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX := by
    rw [← Category.assoc, projBase_fst, Category.assoc]
  refine (heq_of_eq (properChowPushforward_flatPullbackChow_comp_of_isIso C _ _ _
    (pullbackRightPullbackFstIso s t (Scheme.Modules.vectorBundleToBase X 𝒞)).hom _
    (pullback.snd (Scheme.Modules.vectorBundleToBase X 𝒞) (pullback.fst s t)) (projBase 𝒞 s t)
    (pullbackRightPullbackFstIso_hom_projBase 𝒞 s t) _ hB r _ hdF _ _)).trans ?_
  refine (flatPullbackChow_heq_of_eq C _ hjF.symm (inclBase_comp 𝒞 r s t).symm _
    (incl_snd_comp_eq 𝒞 C sX hsq (inclBase 𝒞 r s t)) rfl _
    (relativeDimension_incl_snd 𝒞 r hsq (inclBase 𝒞 r s t)) _ _).trans ?_
  exact (heq_of_eq hL).trans ((chowGroupCast_heq C _ _ _).trans HEq.rfl)

omit [Flat (proj 𝒞)] [Flat (Scheme.Modules.vectorBundleToBase X 𝒞)] in
/-- The cap of `(-1)^{r-1} (r-1)! (j^* ∘ c)` on `t : T ⟶ X₀` is `(-1)^{r-1} (r-1)!` times the
flat pullback along `C ×_{X₀} T ⟶ E ×_{X₀} T` of the cap of `c`. -/
theorem copy_rhsClass_cap_heq {q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
    (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q) {T : Scheme.{u}} (t : T ⟶ X₀)
    [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C (t ≫ sX₀) k) :
    (BivariantClass.copy C (gysinSystemOfInvertible C) _ sX₀ (incl_proj_comp 𝒞 r s) _
        (comp_comp_structureMorphism_eq rfl hs)
        (show -((0 : ℕ) : ℤ) + q = -(r : ℤ) + ((r : ℤ) + q) by push_cast; ring)
        ((((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) • rhsClass 𝒞 r C sX sX₀ s hs c))).cap
        t k β ≍
      ((((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
      flatPullbackChow C (inclBase 𝒞 r s t ≫ pullback.fst (proj 𝒞 ≫ s) t ≫ proj 𝒞 ≫ sX)
        (pullback.fst (proj 𝒞 ≫ s) t ≫ proj 𝒞 ≫ sX) (inclBase 𝒞 r s t) rfl 0
        (relativeDimension_of_isOpenImmersion _) (k - q)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
          (relativeDimension_of_isOpenImmersion _) (k - q)) (c.cap t k β))) := by
  have hjF := inclBase_comp_structure 𝒞 r C sX s t
  refine HEq.symm ?_
  refine HEq.trans ?_ (copy_cap_heq C _ _ _ (incl_proj_comp 𝒞 r s) _ _ _ _ t k β).symm
  refine HEq.trans ?_ (heq_of_eq (congrArg (properChowPushforward C _ _ _ _ _ _)
    (BivariantClass.zsmul_cap C _ _ _ _ _ _ _ _ t k β))).symm
  refine HEq.trans ?_ (heq_of_eq (map_zsmul _ _ _)).symm
  refine chowGroup_zsmul_heq_of_structure C hjF (by push_cast; ring) ?_ _
  refine HEq.symm ?_
  refine (properChowPushforward_heq C _ _ _ _ (show k - (-((0 : ℕ) : ℤ) + q) = k - q + ((0 : ℕ) : ℤ)
    by push_cast; ring) (x := (rhsClass 𝒞 r C sX sX₀ s hs c).cap t k β)
    ((chowGroupDegreeEquiv_heq C _ _ _).trans
      (properChowPushforward_heq C _ _ _ _ (show k - q - -((0 : ℕ) : ℤ) = k - q + ((0 : ℕ) : ℤ)
        by push_cast; ring)
        (x := (inclFlatClass 𝒞 r C sX).cap (pullback.fst (proj 𝒞 ≫ s) t) (k - q) (c.cap t k β))
        (flatPullbackBivariantCap_heq C _ _ _ (vectorBundleIncl_comp_structure 𝒞 r C sX) 0
          (relativeDimension_of_isOpenImmersion _) (flatPullbackDescends C) _ _ _)))).trans ?_
  refine (heq_of_eq (DFunLike.congr_fun (properChowPushforward_comp C _ _ _
    (pullbackRightPullbackFstIso (proj 𝒞 ≫ s) t (vectorBundleIncl 𝒞 r)).hom
    (pullback.map (vectorBundleIncl 𝒞 r ≫ proj 𝒞 ≫ s) t
      (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ s) t (𝟙 _) (𝟙 T) (𝟙 X₀)
      (by simp [incl_proj_comp 𝒞 r s]) (by simp)) _ _ (k - q + ((0 : ℕ) : ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _))
    (flatPullbackChow C (pullback.fst (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞 ≫ s) t) ≫
        Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX) (pullback.fst (proj 𝒞 ≫ s) t ≫ proj 𝒞 ≫ sX)
      (pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞 ≫ s) t))
      (pullbackSnd_comp_structureMorphism_eq C _ _ _ (vectorBundleIncl_comp_structure 𝒞 r C sX)
        _) 0 (relativeDimension_pullback_snd _ _ 0 (relativeDimension_of_isOpenImmersion _))
      (k - q) (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap t k β)))).trans ?_
  refine (heq_of_eq (properChowPushforward_flatPullbackChow_comp_of_isIso C _ _ _ _ _
    (pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞 ≫ s) t)) (inclBase 𝒞 r s t)
    (pullbackRightPullbackFstIso_hom_map_inclBase 𝒞 r s t) _ hjF 0 _
    (relativeDimension_of_isOpenImmersion _) _ _)).trans ?_
  exact flatPullbackChow_heq_of_eq C _ hjF.symm rfl _ rfl rfl _ _ _ _

/-- `p^* ∘ π_* ∘ (c_r(i_*𝒪_X) ∘ c) = (-1)^{r-1} (r-1)! (j^* ∘ c)` as bivariant classes. -/
theorem lhsClass_eq {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
    (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q) :
    lhsClass 𝒞 r C sX sX₀ s hs c =
      BivariantClass.copy C (gysinSystemOfInvertible C) _ sX₀ (incl_proj_comp 𝒞 r s) _
        (comp_comp_structureMorphism_eq rfl hs)
        (show -((0 : ℕ) : ℤ) + q = -(r : ℤ) + ((r : ℤ) + q) by push_cast; ring)
        ((((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) • rhsClass 𝒞 r C sX sX₀ s hs c)) := by
  apply BivariantClass.ext
  intro T t _ k β
  exact eq_of_heq ((lhsClass_cap_heq 𝒞 r C sX sX₀ s hs c t k β).trans
    (copy_rhsClass_cap_heq 𝒞 r C sX sX₀ s hs c t k β).symm)

end Classes

/-! ### Stacks 0FEF (2) at the level of bivariant classes -/

section Main

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0FEF (2), as an equality of bivariant classes.** Let `π : E ⟶ X` be the projective
completion of a locally free module `𝒞` of rank `r`, `i : X ⟶ E` its zero section,
`j : C ⟶ E` and `p : C ⟶ X` the inclusion and the structure morphism of the vector bundle
`C = Spec_X(Sym^*(𝒞))`. For every `s : X ⟶ X₀` and every bivariant class `c ∈ A^q(E ⟶ X₀)`,

  `p^* ∘ π_* ∘ (c_r(i_*𝒪_X) ∘ c) = (-1)^{r-1} (r-1)! (j^* ∘ c)`  in `A^q(C ⟶ X₀)`.

Here `c_r(i_*𝒪_X) ∈ A^r(E)` is the Chern class of Stacks 0F9E, `∘` the composition of Stacks
0B75, `π_*` the pushforward of Stacks 0EPK and `p^* ∈ A^{-r}(C ⟶ X)`, `j^* ∈ A^0(C ⟶ E)` the
flat pullback classes of Stacks 0B78; the two sides are classes for the equal morphisms
`p ≫ s = j ≫ π ≫ s` and of the equal degrees `-r + (r + q) = -0 + q`, compared through the
transport `Stacks.Chow.BivariantClass.copy`. This is the form in which the source composes the
identity `p^* ∘ π_* ∘ c_r(i_*𝒪_X) = (-1)^{r-1} (r-1)! j^*` with a class on its right (Stacks 0FEG);
by the extensionality of Stacks 0B76 it is checked on the caps, which are classes on the base
changes `E ×_{X₀} T = E ×_X (X ×_{X₀} T)`, where it is the cartesian-square form
`flatPullbackChow_properChowPushforward_perfectChernClass_of_isPullback` of the second conclusion.
-/
@[stacks 0FEF "clause (2), as an equality of bivariant classes after composing with any \
c ∈ A^*(E → X₀)"]
theorem bivariantClass_zeroSecObject {X₀ : Scheme.{u}} (sX₀ : X₀ ⟶ C.S) [LocallyOfFiniteType sX₀]
    (s : X ⟶ X₀) [LocallyOfFiniteType s] (hs : s ≫ sX₀ = sX) :
    haveI := locallyOfFiniteType_proj 𝒞 r
    haveI := flat_proj 𝒞 r
    haveI := locallyOfFiniteType_vectorBundleToBase 𝒞 r
    haveI := flat_vectorBundleToBase 𝒞 r
    ∀ {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
      (proj 𝒞 ≫ s) (comp_comp_structureMorphism_eq rfl hs) q),
      bivariantCompositeOfInvertible C _ sX sX₀ _ s rfl hs (-(r : ℤ)) ((r : ℤ) + q)
          (flatPullbackBivariantClassOfInvertible C
            (Scheme.Modules.vectorBundleToBase X 𝒞 ≫ sX) sX _ rfl r
            (relativeDimension_vectorBundleToBase 𝒞 r))
          (canonicalBivariantProperPushforward C (proj 𝒞 ≫ sX) sX sX₀ (proj 𝒞) s rfl hs
            ((r : ℤ) + q)
            (BivariantClass.copy C (gysinSystemOfInvertible C) (proj 𝒞 ≫ sX) sX₀
              (Category.id_comp (proj 𝒞 ≫ s)) _ _ rfl
              (bivariantCompositeOfInvertible C (proj 𝒞 ≫ sX) (proj 𝒞 ≫ sX) sX₀ (𝟙 _)
                (proj 𝒞 ≫ s) (Category.id_comp _) (comp_comp_structureMorphism_eq rfl hs)
                (r : ℤ) q
                (perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)
                  r) c))) =
        BivariantClass.copy C (gysinSystemOfInvertible C) _ sX₀ (incl_proj_comp 𝒞 r s) _
          (comp_comp_structureMorphism_eq rfl hs)
          (show -((0 : ℕ) : ℤ) + q = -(r : ℤ) + ((r : ℤ) + q) by push_cast; ring)
          ((((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
            bivariantCompositeOfInvertible C _ (proj 𝒞 ≫ sX) sX₀ (vectorBundleIncl 𝒞 r)
              (proj 𝒞 ≫ s) (vectorBundleIncl_comp_structure 𝒞 r C sX)
              (comp_comp_structureMorphism_eq rfl hs) (-((0 : ℕ) : ℤ)) q
              (flatPullbackBivariantClassOfInvertible C _ _ _
                (vectorBundleIncl_comp_structure 𝒞 r C sX) 0
                (relativeDimension_of_isOpenImmersion _)) c)) := by
  have := locallyOfFiniteType_proj 𝒞 r
  have := flat_proj 𝒞 r
  have := locallyOfFiniteType_vectorBundleToBase 𝒞 r
  have := flat_vectorBundleToBase 𝒞 r
  intro q c
  exact lhsClass_eq 𝒞 r C sX sX₀ s hs c

end Main

end Stacks.Chow.ProjectiveCompletion

end
