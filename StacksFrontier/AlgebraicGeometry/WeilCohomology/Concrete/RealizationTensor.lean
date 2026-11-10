module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of a tensor product of correspondences

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with coefficient
field of characteristic zero, and let `G` be the functor of the proof of Stacks 0FHL on
correspondences of degree zero. The tensor product of correspondences acts as the tensor product
of the actions through the Künneth maps:

  `G(c ⊗ c')(pr₁^*a ∪ pr₂^*a') = pr₁^*G(c)(a) ∪ pr₂^*G(c')(a')`,

the step "the Künneth axiom (B)(a) shows our functor is compatible with tensor products" of the
source. On the blocks this is `blockAct_tensor` together with the class of a tensor product of
correspondences (`corrClass_tensorBlock`), the piece `X_d × X'_{d'}` of `(X × X')_{d+d'}` being
handled by extension by zero.

## Main results

* `Stacks.WeilCohomology.WeilData.corrMap_tensor`.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow MonoidalCategory

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-! ### Pushforward of correspondences along products of morphisms -/

/-- The pushforward `(i × j)_* : Corrʳ(U, V) → Corrʳ(P, Q)` of rational correspondences along
the product of morphisms `i : U ⟶ P`, `j : V ⟶ Q` of smooth projective schemes. -/
def pushCorr {U V P Q : (SmoothProjectiveScheme k).FullSubcategory} (i : U ⟶ P) (j : V ⟶ Q)
    (e r : ℤ) :
    Correspondence (fieldChowSituation k) U.obj.hom V.obj.hom e r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) P.obj.hom Q.obj.hom e r :=
  haveI := SmoothProjectiveScheme.isProper_hom_left (prodLift (fst U V ≫ i) (snd U V ≫ j))
  (properChowPushforward (fieldChowSituation k) (prod U V).obj.hom (prod P Q).obj.hom
    (prodLift (fst U V ≫ i) (snd U V ≫ j)).hom.left (Over.w _) (e - r)
    (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap.baseChange ℚ

include hA hC in
/-- **The class of a pushforward along a product of morphisms, in trace form** ((C)(b)): for
`U × V` and `P × Q` nonempty and equidimensional of the same dimension,
`∫_{P × Q} γ((i × j)_*t) ∪ v = ∫_{U × V} γ(t) ∪ (i × j)^*v`. -/
theorem traceProj_corrClass_pushCorr {U V P Q : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ}
    (hU : IsNonemptyEquidimensional U d) (hV : IsNonemptyEquidimensional V e)
    (hP : IsNonemptyEquidimensional P d) (hQ : IsNonemptyEquidimensional Q e) (i : U ⟶ P)
    (j : V ⟶ Q) (E r c : ℤ) (hc : c = ((d + e : ℕ) : ℤ) - (E - r))
    (t : Correspondence (fieldChowSituation k) U.obj.hom V.obj.hom E r) (v : W.H (prod P Q)) :
    W.traceProj (prod P Q) (d + e) (isNonemptyEquidimensional_prod hP hQ)
        (W.corrClass P Q E r c (pushCorr i j E r t) * v) =
      W.traceProj (prod U V) (d + e) (isNonemptyEquidimensional_prod hU hV)
        (W.corrClass U V E r c t * W.pull (prodLift (fst U V ≫ i) (snd U V ≫ j)) v) := by
  have := SmoothProjectiveScheme.isProper_hom_left (prodLift (fst U V ≫ i) (snd U V ≫ j))
  induction t using TensorProduct.inductionOn with
  | add t t' h h' => rw [map_add, map_add, add_mul, map_add, h, h', map_add, add_mul, map_add]
  | tmul q α =>
    have h₁ : W.corrClass P Q E r c (pushCorr i j E r (q ⊗ₜ α)) =
        (q : F) • W.cycleClassRing (prod P Q) c (chowGroupToCodimension (prod P Q).obj.hom (E - r) c
          (properChowPushforward (fieldChowSituation k) (prod U V).obj.hom (prod P Q).obj.hom
            (prodLift (fst U V ≫ i) (snd U V ≫ j)).hom.left (Over.w _) (E - r)
            (properPushforwardDescends _ _ _ _ _ _) α)) := rfl
    have h₂ : W.corrClass U V E r c (q ⊗ₜ α) =
        (q : F) • W.cycleClassRing (prod U V) c
          (chowGroupToCodimension (prod U V).obj.hom (E - r) c α) := rfl
    rw [h₁, h₂, smul_mul_assoc, map_smul, smul_mul_assoc, map_smul]
    congr 1
    exact traceProj_cycleClassRing_properChowPushforward hA hC
      (isNonemptyEquidimensional_prod hU hV) (isNonemptyEquidimensional_prod hP hQ)
      (prodLift (fst U V ≫ i) (snd U V ≫ j)).hom.left (Over.w _) (E - r) c hc α v

/-- **The action of a pushed-forward class is an extension by zero**: if
`∫_{P × Q} w ∪ v = ∫_{U × V} z ∪ (i × j)^*v` with `j` an open and closed immersion between
schemes of the same dimension, then `blockAct w a = j_!(blockAct z (i^*a))`. -/
theorem coe_blockAct_eq_extendByZero {P Q U V : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ}
    (hP : IsNonemptyEquidimensional P d) (hQ : IsNonemptyEquidimensional Q e)
    (hU : IsNonemptyEquidimensional U d) (hV : IsNonemptyEquidimensional V e) (i : U ⟶ P)
    (j : V ⟶ Q) [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left]
    {w : W.H (prod P Q)} {z : W.H (prod U V)} (hz : z ∈ W.grade (prod U V) (2 * d))
    (hw : ∀ v : W.H (prod P Q),
      W.traceProj (prod P Q) (d + e) (isNonemptyEquidimensional_prod hP hQ) (w * v) =
        W.traceProj (prod U V) (d + e) (isNonemptyEquidimensional_prod hU hV)
          (z * W.pull (prodLift (fst U V ≫ i) (snd U V ≫ j)) v))
    {n : ℤ} (a : W.grade P n) :
    (W.blockAct hA.perfectPairing hP hQ w n a : W.H Q) =
      extendByZero hA hB hC j (W.blockAct hA.perfectPairing hU hV z n (W.pullDeg i n a)) := by
  have hm := extendByZero_mem (hA := hA) (hB := hB) (hC := hC) j
    (W.blockAct hA.perfectPairing hU hV z n (W.pullDeg i n a)).2
  suffices h : W.blockAct hA.perfectPairing hP hQ w n a = ⟨_, hm⟩ from congrArg Subtype.val h
  refine eq_of_traceProj_mul_eq hA.perfectPairing hQ fun b ↦ ?_
  rw [blockAct_prodMap hA.perfectPairing hP hQ hU hV i j hz hw a b]
  exact (traceProj_extendByZero_mul (hA := hA) (hB := hB) (hC := hC) j hQ hV _ _).symm

/-- Extension by zero along equal morphisms. -/
theorem extendByZero_congr {V X : (SmoothProjectiveScheme k).FullSubcategory} {j j' : V ⟶ X}
    (h : j = j')
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] [IsOpenImmersion j'.hom.left]
    [IsClosedImmersion j'.hom.left] (x : W.H V) :
    extendByZero hA hB hC j x = extendByZero hA hB hC j' x := by
  subst h
  rfl

/-! ### Products of parts -/

/-- The inclusion `X_d × X'_{d'} ⟶ (X × X')_{d+d'}` of a product of parts into the part of the
product (`Stacks.WeilCohomology.partProdHom`). -/
def partProdι (X X' : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) :
    prod (part X d) (part X' d') ⟶ part (prod X X') (d + d') :=
  ObjectProperty.homMk (Over.homMk (partProdHom k X.obj.hom X'.obj.hom d d')
    (partProdHom_comp_partBase k X.obj.hom X'.obj.hom d d'))

/-- The inclusion `partProdι X X' d d'` of a product of parts is an open immersion. -/
instance (X X' : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) :
    IsOpenImmersion (partProdι X X' d d').hom.left :=
  inferInstanceAs (IsOpenImmersion (partProdHom k X.obj.hom X'.obj.hom d d'))

/-- The inclusion `partProdι X X' d d'` of a product of parts is a closed immersion. -/
instance (X X' : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) :
    IsClosedImmersion (partProdι X X' d d').hom.left := by
  have := SmoothProjectiveScheme.isProper_hom_left (partProdι X X' d d')
  exact IsClosedImmersion.of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

/-- The composite `X_d × X'_{d'} ⟶ (X × X')_{d+d'} ⟶ X × X'` is an open immersion. -/
instance (X X' : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) :
    IsOpenImmersion (partProdι X X' d d' ≫ partι (prod X X') (d + d')).hom.left :=
  inferInstanceAs (IsOpenImmersion ((partProdι X X' d d').hom.left ≫
    (partι (prod X X') (d + d')).hom.left))

/-- The composite `X_d × X'_{d'} ⟶ (X × X')_{d+d'} ⟶ X × X'` is a closed immersion. -/
instance (X X' : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) :
    IsClosedImmersion (partProdι X X' d d' ≫ partι (prod X X') (d + d')).hom.left :=
  inferInstanceAs (IsClosedImmersion ((partProdι X X' d d').hom.left ≫
    (partι (prod X X') (d + d')).hom.left))

/-- `X_d × X'_{d'} ⟶ (X × X')_{d+d'} ⟶ X × X'` is the product of the inclusions of the parts. -/
theorem partProdι_partι (X X' : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) :
    partProdι X X' d d' ≫ partι (prod X X') (d + d') =
      prodLift (fst (part X d) (part X' d') ≫ partι X d)
        (snd (part X d) (part X' d') ≫ partι X' d') :=
  SmoothProjectiveScheme.hom_ext_left (partProdHom_ι k X.obj.hom X'.obj.hom d d')

/-- The blocks of `Corr(X × X', Y × Y')`, read on the parts of the products. -/
def tensorBlockEquiv (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (D E : ℕ) (r : ℤ) :
    Correspondence (fieldChowSituation k) (partBase (prodBase X.obj.hom X'.obj.hom) D)
        (partBase (prodBase Y.obj.hom Y'.obj.hom) E) E r ≃ₗ[ℚ]
      Correspondence (fieldChowSituation k) (part (prod X X') D).obj.hom
        (part (prod Y Y') E).obj.hom E r :=
  LinearEquiv.refl ℚ _

/-- The products of parts of `X × X'` and `Y × Y'`, read as products of the smooth projective
schemes `X_d`, `X'_{d'}`, `Y_e`, `Y'_{e'}`. -/
def prodPartEquiv (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (d d' e e' : ℕ) (r : ℤ) :
    Correspondence (fieldChowSituation k)
        (prodBase (partBase X.obj.hom d) (partBase X'.obj.hom d'))
        (prodBase (partBase Y.obj.hom e) (partBase Y'.obj.hom e')) ((e + e' : ℕ) : ℤ) r ≃ₗ[ℚ]
      Correspondence (fieldChowSituation k) (prod (part X d) (part X' d')).obj.hom
        (prod (part Y e) (part Y' e')).obj.hom ((e + e' : ℕ) : ℤ) r :=
  LinearEquiv.refl ℚ _

/-- Correspondences between products `X × X'` and `Y × Y'`, read on the smooth projective schemes
`X × X'`, `Y × Y'`. -/
def tensorEquiv (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    Corr k (prodBase X.obj.hom X'.obj.hom) (prodBase Y.obj.hom Y'.obj.hom) r ≃ₗ[ℚ]
      Corr k (prod X X').obj.hom (prod Y Y').obj.hom r :=
  LinearEquiv.refl ℚ _

/-- The realization of a tensor product, read through `tensorEquiv`. -/
theorem corrMap_tensor_eq (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (c : Corr k X.obj.hom Y.obj.hom 0) (c' : Corr k X'.obj.hom Y'.obj.hom 0) :
    corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) n
        (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
          c c') =
      corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) n
        (tensorEquiv X X' Y Y' (0 + 0) (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
          (canonicalDiagonalClassFamily k) 0 0 c c')) :=
  rfl

/-- A pure block of a correspondence between products, read through `corrMap`. -/
theorem corrMap_tensorEquiv_lof_lof (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (r n : ℤ) (D E : ℕ)
    (t : Correspondence (fieldChowSituation k) (partBase (prodBase X.obj.hom X'.obj.hom) D)
        (partBase (prodBase Y.obj.hom Y'.obj.hom) E) E r) :
    corrMap hA hB hC (prod X X') (prod Y Y') r n
        (tensorEquiv X X' Y Y' r (DirectSum.lof ℚ ℕ _ D (DirectSum.lof ℚ ℕ _ E t))) =
      blockMap hA hB hC (prod X X') (prod Y Y') D E r n (tensorBlockEquiv X X' Y Y' D E r t) :=
  corrMap_lof_lof hA hB hC (prod X X') (prod Y Y') r n D E _

/-- `tensor_lof_lof` for smooth projective schemes over `k` and the canonical diagonal classes. -/
theorem tensor_lof_lof_canonical (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (d e d' e' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (x' : Correspondence (fieldChowSituation k) (partBase X'.obj.hom d') (partBase Y'.obj.hom e')
      e' 0) :
    tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x')) =
      DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (e + e')
        (tensorBlockInclusion k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom d d' e e' (0 + 0)
          (tensorBlock k (partBase X.obj.hom d) (partBase X'.obj.hom d') (partBase Y.obj.hom e)
            (partBase Y'.obj.hom e') (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
            (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
            0 0 x x'))) :=
  tensor_lof_lof k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom _ 0 0 d e d' e' x x'

/-- A pure block of the tensor product, read through `corrMap`. -/
theorem corrMap_tensor_lof_lof (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (d e d' e' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (x' : Correspondence (fieldChowSituation k) (partBase X'.obj.hom d') (partBase Y'.obj.hom e')
      e' 0) :
    corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) n
        (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))) =
      blockMap hA hB hC (prod X X') (prod Y Y') (d + d') (e + e') (0 + 0) n
        (tensorBlockEquiv X X' Y Y' (d + d') (e + e') (0 + 0)
          (tensorBlockInclusion k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom d d' e e' (0 + 0)
            (tensorBlock k (partBase X.obj.hom d) (partBase X'.obj.hom d') (partBase Y.obj.hom e)
              (partBase Y'.obj.hom e') (canonicalDiagonalClassFamily k)
              (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
              (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
              0 0 x x'))) :=
  (corrMap_tensor_eq hA hB hC X X' Y Y' n _ _).trans
    ((congrArg (fun t ↦ corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) n
      (tensorEquiv X X' Y Y' (0 + 0) t)) (tensor_lof_lof_canonical X X' Y Y' d e d' e' x x')).trans
    (corrMap_tensorEquiv_lof_lof hA hB hC X X' Y Y' (0 + 0) n (d + d') (e + e') _))

/-- The pushed block is the pushforward along the products of the inclusions of the parts. -/
theorem tensorBlockEquiv_tensorBlockInclusion
    (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (d d' e e' : ℕ) (r : ℤ)
    (t : Correspondence (fieldChowSituation k)
      (prodBase (partBase X.obj.hom d) (partBase X'.obj.hom d'))
      (prodBase (partBase Y.obj.hom e) (partBase Y'.obj.hom e')) ((e + e' : ℕ) : ℤ) r) :
    tensorBlockEquiv X X' Y Y' (d + d') (e + e') r
        (tensorBlockInclusion k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom d d' e e' r t) =
      pushCorr (partProdι X X' d d') (partProdι Y Y' e e') ((e + e' : ℕ) : ℤ) r
        (prodPartEquiv X X' Y Y' d d' e e' r t) :=
  rfl

/-- The tensor product of blocks, read on the parts. -/
theorem prodPartEquiv_tensorBlock (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (d d' e e' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (x' : Correspondence (fieldChowSituation k) (partBase X'.obj.hom d') (partBase Y'.obj.hom e')
      e' 0) :
    prodPartEquiv X X' Y Y' d d' e e' (0 + 0)
        (tensorBlock k (partBase X.obj.hom d) (partBase X'.obj.hom d') (partBase Y.obj.hom e)
          (partBase Y'.obj.hom e') (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
          (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
          0 0 x x') =
      tensorBlock k (part X d).obj.hom (part X' d').obj.hom (part Y e).obj.hom
          (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
          (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
          0 0 (blockEquiv X Y d e 0 x) (blockEquiv X' Y' d' e' 0 x') :=
  rfl

/-- Extending by zero from `Y_e × Y'_{e'}` to `(Y × Y')_{e+e'}` and then to `Y × Y'`. -/
theorem extendByZero_partι_partProdι (Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (e e' : ℕ)
    (x : W.H (prod (part Y e) (part Y' e'))) :
    extendByZero hA hB hC (partι (prod Y Y') (e + e'))
        (extendByZero hA hB hC (partProdι Y Y' e e') x) =
      extendByZero hA hB hC (prodLift (fst (part Y e) (part Y' e') ≫ partι Y e)
        (snd (part Y e) (part Y' e') ≫ partι Y' e')) x :=
  (extendByZero_comp (hA := hA) (hB := hB) (hC := hC) (partProdι Y Y' e e')
    (partι (prod Y Y') (e + e')) x).symm.trans
    (extendByZero_congr hA hB hC (partProdι_partι Y Y' e e') x)

/-- **The tensor law on a block** of nonempty parts `X_d, X'_{d'}, Y_e, Y'_{e'}`. -/
theorem coe_blockMap_pushCorr_tensorBlock (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    {d d' e e' : ℕ} (hXd : Nonempty (part X d).obj.left) (hX'd' : Nonempty (part X' d').obj.left)
    (hYe : Nonempty (part Y e).obj.left) (hY'e' : Nonempty (part Y' e').obj.left)
    (y : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e 0)
    (y' : Correspondence (fieldChowSituation k) (part X' d').obj.hom (part Y' e').obj.hom e' 0)
    {p q : ℤ} (a : W.grade X p) (a' : W.grade X' q) :
    (blockMap hA hB hC (prod X X') (prod Y Y') (d + d') (e + e') (0 + 0) (p + q)
        (pushCorr (partProdι X X' d d') (partProdι Y Y' e e') ((e + e' : ℕ) : ℤ) (0 + 0)
          (tensorBlock k (part X d).obj.hom (part X' d').obj.hom (part Y e).obj.hom
            (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
            (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
            0 0 y y'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (blockMap hA hB hC X Y d e 0 p y a) *
        W.pull (snd Y Y') (blockMap hA hB hC X' Y' d' e' 0 q y' a') := by
  have hXd₁ := isNonemptyEquidimensional_part X hXd
  have hX'd'₁ := isNonemptyEquidimensional_part X' hX'd'
  have hYe₁ := isNonemptyEquidimensional_part Y hYe
  have hY'e'₁ := isNonemptyEquidimensional_part Y' hY'e'
  have hU := isNonemptyEquidimensional_prod hXd₁ hX'd'₁
  have hV := isNonemptyEquidimensional_prod hYe₁ hY'e'₁
  have hPn : Nonempty (part (prod X X') (d + d')).obj.left :=
    ⟨(partProdι X X' d d').hom.left (Classical.choice hU.nonempty)⟩
  have hQn : Nonempty (part (prod Y Y') (e + e')).obj.left :=
    ⟨(partProdι Y Y' e e').hom.left (Classical.choice hV.nonempty)⟩
  have hP := isNonemptyEquidimensional_part (prod X X') hPn
  have hQ := isNonemptyEquidimensional_part (prod Y Y') hQn
  have hz : (W.corrClass (prod (part X d) (part X' d')) (prod (part Y e) (part Y' e'))
      ((e + e' : ℕ) : ℤ) (0 + 0) ((d + d' : ℕ) : ℤ) (tensorBlock k (part X d).obj.hom (part X'
          d').obj.hom (part Y e).obj.hom
      (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
      (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e') 0 0 y
          y')) ∈ W.grade _ (2 * ((d + d' : ℕ) : ℤ)) := W.corrClass_mem _ _ _ _ _ _
  have hz₁ := W.corrClass_mem (part X d) (part Y e) e 0 d y
  have hz₂ := W.corrClass_mem (part X' d') (part Y' e') e' 0 d' y'
  have h4 : (W.corrClass (prod (part X d) (part X' d')) (prod (part Y e) (part Y' e'))
      ((e + e' : ℕ) : ℤ) (0 + 0) ((d + d' : ℕ) : ℤ) (tensorBlock k (part X d).obj.hom (part X'
          d').obj.hom (part Y e).obj.hom
      (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
      (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e') 0 0 y
          y')) = W.pull (prodTensorPr₁₃ (part X d) (part X' d') (part Y e) (part Y' e'))
              (W.corrClass (part X d) (part Y e) e 0 d y) *
      W.pull (prodTensorPr₂₄ (part X d) (part X' d') (part Y e) (part Y' e')) (W.corrClass (part X'
          d') (part Y' e') e' 0 d' y') :=
    corrClass_tensorBlock hA hC hXd₁ hX'd'₁ hYe₁ hY'e'₁ y y'
  -- the restriction of `pr₁^*a ∪ pr₂^*a'` to `X_d × X'_{d'}`
  have h3 : W.pullDeg (partProdι X X' d d') (p + q)
      (W.pullDeg (partι (prod X X') (d + d')) (p + q)
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩) =
      ⟨W.pull (fst (part X d) (part X' d')) (W.pullDeg (partι X d) p a : W.H (part X d)) *
          W.pull (snd (part X d) (part X' d')) (W.pullDeg (partι X' d') q a' : W.H (part X' d')),
        SetLike.GradedMul.mul_mem (W.pull_grade _ p _ (W.pullDeg (partι X d) p a).2)
          (W.pull_grade _ q _ (W.pullDeg (partι X' d') q a').2)⟩ := by
    apply Subtype.ext
    simp only [coe_pullDeg, map_mul, pull_pull]
    rw [← Category.assoc, partProdι_partι, prodLift_fst, ← Category.assoc, partProdι_partι,
      prodLift_snd]
  -- the left side
  have hw := traceProj_corrClass_pushCorr hA hC hU hV hP hQ (partProdι X X' d d')
    (partProdι Y Y' e e') ((e + e' : ℕ) : ℤ) (0 + 0) ((d + d' : ℕ) : ℤ) (by push_cast; ring)
    (tensorBlock k (part X d).obj.hom (part X' d').obj.hom (part Y e).obj.hom
      (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
      (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e') 0 0 y y')
  have hL : (blockMap hA hB hC (prod X X') (prod Y Y') (d + d') (e + e') (0 + 0) (p + q)
        (pushCorr (partProdι X X' d d') (partProdι Y Y' e e') ((e + e' : ℕ) : ℤ) (0 + 0)
          (tensorBlock k (part X d).obj.hom (part X' d').obj.hom (part Y e).obj.hom
      (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
      (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e') 0 0 y y'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      extendByZero hA hB hC (partι (prod Y Y') (e + e'))
        (extendByZero hA hB hC (partProdι Y Y' e e')
          (W.pull (fst (part Y e) (part Y' e'))
              (W.blockAct hA.perfectPairing hXd₁ hYe₁ (W.corrClass (part X d) (part Y e) e 0 d y) p
                  (W.pullDeg (partι X d) p a)) *
            W.pull (snd (part Y e) (part Y' e'))
              (W.blockAct hA.perfectPairing hX'd'₁ hY'e'₁ (W.corrClass (part X' d') (part Y' e') e'
                  0 d' y') q (W.pullDeg (partι X' d') q a')))) := by
    rw [blockMap_of_nonempty hA hB hC (p + q) hPn hQn, LinearMap.comp_apply, LinearMap.comp_apply,
      coe_extendDeg, coe_blockAct_eq_extendByZero hA hB hC hP hQ hU hV _ _ hz hw, h3]
    congr 2
    refine Eq.trans ?_ (blockAct_tensor hA hB hC hXd₁ hX'd'₁ hYe₁ hY'e'₁ hz₁ hz₂
      (W.pullDeg (partι X d) p a) (W.pullDeg (partι X' d') q a'))
    congr 2
    exact congrArg (fun z ↦ W.blockAct hA.perfectPairing hU hV z (p + q)) h4
  -- the right side
  have hR : W.pull (fst Y Y') (blockMap hA hB hC X Y d e 0 p y a) *
        W.pull (snd Y Y') (blockMap hA hB hC X' Y' d' e' 0 q y' a') =
      extendByZero hA hB hC (prodLift (fst (part Y e) (part Y' e') ≫ partι Y e)
          (snd (part Y e) (part Y' e') ≫ partι Y' e'))
        (W.pull (fst (part Y e) (part Y' e'))
            (W.blockAct hA.perfectPairing hXd₁ hYe₁ (W.corrClass (part X d) (part Y e) e 0 d y) p
                (W.pullDeg (partι X d) p a)) *
          W.pull (snd (part Y e) (part Y' e'))
            (W.blockAct hA.perfectPairing hX'd'₁ hY'e'₁ (W.corrClass (part X' d') (part Y' e') e' 0
                d' y') q (W.pullDeg (partι X' d') q a'))) := by
    rw [blockMap_of_nonempty hA hB hC p hXd hYe, blockMap_of_nonempty hA hB hC q hX'd' hY'e']
    exact pull_fst_extendByZero_mul_pull_snd_extendByZero (hA := hA) (hB := hB) (hC := hC) _ _ _ _
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact extendByZero_partι_partProdι hA hB hC Y Y' e e' _


/-- A correspondence between smooth projective schemes one of which is empty vanishes. -/
theorem correspondence_eq_zero_of_isEmpty {A B : (SmoothProjectiveScheme k).FullSubcategory}
    (h : IsEmpty A.obj.left ∨ IsEmpty B.obj.left) {e r : ℤ}
    (t : Correspondence (fieldChowSituation k) A.obj.hom B.obj.hom e r) : t = 0 := by
  have hP : ↥(Limits.pullback A.obj.hom B.obj.hom) → False := fun z ↦
    h.elim (fun h ↦ h.false ((Limits.pullback.fst A.obj.hom B.obj.hom) z))
      (fun h ↦ h.false ((Limits.pullback.snd A.obj.hom B.obj.hom) z))
  induction t using TensorProduct.inductionOn with
  | tmul q α => rw [chowGroup_eq_zero_of_isEmpty hP α, TensorProduct.tmul_zero]
  | add t t' h h' => rw [h, h', add_zero]

/-- A product with an empty factor is empty. -/
theorem isEmpty_prod_of_isEmpty {A B : (SmoothProjectiveScheme k).FullSubcategory}
    (h : IsEmpty A.obj.left ∨ IsEmpty B.obj.left) : IsEmpty (prod A B).obj.left := by
  rcases h with h | h
  · exact ⟨fun z ↦ h.false ((fst A B).hom.left z)⟩
  · exact ⟨fun z ↦ h.false ((snd A B).hom.left z)⟩

/-- The pushforward of a correspondence on an empty product vanishes. -/
theorem pushCorr_eq_zero_of_isEmpty {U V P Q : (SmoothProjectiveScheme k).FullSubcategory}
    (i : U ⟶ P) (j : V ⟶ Q) (E r : ℤ) (h : IsEmpty U.obj.left ∨ IsEmpty V.obj.left)
    (t : Correspondence (fieldChowSituation k) U.obj.hom V.obj.hom E r) :
    pushCorr i j E r t = 0 := by
  rw [correspondence_eq_zero_of_isEmpty h t, map_zero]

/-- The action of a pushforward from an empty product vanishes. -/
theorem blockMap_pushCorr_eq_zero {X X' Y Y' U V : (SmoothProjectiveScheme k).FullSubcategory}
    {D E : ℕ}
    (i : U ⟶ part (prod X X') D) (j : V ⟶ part (prod Y Y') E) {r : ℤ} (n : ℤ)
    (h : IsEmpty U.obj.left ∨ IsEmpty V.obj.left)
    (t : Correspondence (fieldChowSituation k) U.obj.hom V.obj.hom E r) :
    blockMap hA hB hC (prod X X') (prod Y Y') D E r n (pushCorr i j E r t) = 0 := by
  rw [pushCorr_eq_zero_of_isEmpty i j E r h t, map_zero]

/-- **The tensor law on a block**, in all cases. -/
theorem coe_blockMap_pushCorr_tensorBlock' (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    {d d' e e' : ℕ}
    (y : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e 0)
    (y' : Correspondence (fieldChowSituation k) (part X' d').obj.hom (part Y' e').obj.hom e' 0)
    {p q : ℤ} (a : W.grade X p) (a' : W.grade X' q) :
    (blockMap hA hB hC (prod X X') (prod Y Y') (d + d') (e + e') (0 + 0) (p + q)
        (pushCorr (partProdι X X' d d') (partProdι Y Y' e e') ((e + e' : ℕ) : ℤ) (0 + 0)
          (tensorBlock k (part X d).obj.hom (part X' d').obj.hom (part Y e).obj.hom
            (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
            (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
            0 0 y y'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (blockMap hA hB hC X Y d e 0 p y a) *
        W.pull (snd Y Y') (blockMap hA hB hC X' Y' d' e' 0 q y' a') := by
  by_cases hne : Nonempty (part X d).obj.left ∧ Nonempty (part X' d').obj.left ∧
      Nonempty (part Y e).obj.left ∧ Nonempty (part Y' e').obj.left
  · exact coe_blockMap_pushCorr_tensorBlock hA hB hC X X' Y Y' hne.1 hne.2.1 hne.2.2.1 hne.2.2.2
      y y' a a'
  simp only [not_and_or, not_nonempty_iff] at hne
  have hL := blockMap_pushCorr_eq_zero hA hB hC (partProdι X X' d d') (partProdι Y Y' e e')
    (p + q) (by
      rcases hne with h | h | h | h
      exacts [.inl (isEmpty_prod_of_isEmpty (.inl h)), .inl (isEmpty_prod_of_isEmpty (.inr h)),
        .inr (isEmpty_prod_of_isEmpty (.inl h)), .inr (isEmpty_prod_of_isEmpty (.inr h))])
    (tensorBlock k (part X d).obj.hom (part X' d').obj.hom (part Y e).obj.hom
      (part Y' e').obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_partBase X.obj.hom d) (relativeDimension_partBase X'.obj.hom d')
      (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Y'.obj.hom e')
      0 0 y y')
  rw [hL]
  rcases hne with h | h | h | h
  · simp only [blockMap_of_isEmpty_left hA hB hC _ (not_nonempty_iff.2 h), LinearMap.zero_apply,
      ZeroMemClass.coe_zero, AddMonoidHom.zero_apply, map_zero, zero_mul]
  · simp only [blockMap_of_isEmpty_left hA hB hC _ (not_nonempty_iff.2 h), LinearMap.zero_apply,
      ZeroMemClass.coe_zero, AddMonoidHom.zero_apply, map_zero, mul_zero]
  · simp only [blockMap_of_isEmpty_right hA hB hC _ (not_nonempty_iff.2 h), LinearMap.zero_apply,
      ZeroMemClass.coe_zero, AddMonoidHom.zero_apply, map_zero, zero_mul]
  · simp only [blockMap_of_isEmpty_right hA hB hC _ (not_nonempty_iff.2 h), LinearMap.zero_apply,
      ZeroMemClass.coe_zero, AddMonoidHom.zero_apply, map_zero, mul_zero]

/-- **The tensor law on pure blocks.** -/
theorem corrMap_tensor_lof (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) (d e d' e' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (x' : Correspondence (fieldChowSituation k) (partBase X'.obj.hom d') (partBase Y'.obj.hom e')
      e' 0) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof
              ℚ ℕ _ e' x')))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _
            e' x')) a') := by
  have h1 := corrMap_tensor_lof_lof hA hB hC X X' Y Y' (p + q) d e d' e' x x'
  rw [h1]
  refine (coe_blockMap_pushCorr_tensorBlock' hA hB hC X X' Y Y' (blockEquiv X Y d e 0 x)
    (blockEquiv X' Y' d' e' 0 x') a a').trans ?_
  rw [corrMap_lof_lof, corrMap_lof_lof]

/-- The tensor product of correspondences is additive in the first variable. -/
theorem tensor_add_left_canonical (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (c₁ c₂ : Corr k X.obj.hom Y.obj.hom 0) (c' : Corr k X'.obj.hom Y'.obj.hom 0) :
    tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0 (c₁ +
        c₂) c' = tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily
            k) 0 0 c₁ c' + tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
                (canonicalDiagonalClassFamily k) 0 0 c₂ c' :=
  LinearMap.map_add₂ _ c₁ c₂ c'

/-- The tensor product of correspondences is additive in the second variable. -/
theorem tensor_add_right_canonical (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (c : Corr k X.obj.hom Y.obj.hom 0) (c₁ c₂ : Corr k X'.obj.hom Y'.obj.hom 0) :
    tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0 c (c₁ +
        c₂) = tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0
            0 c c₁ + tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
                (canonicalDiagonalClassFamily k) 0 0 c c₂ :=
  LinearMap.map_add _ c₁ c₂

/-- `G` is additive in the correspondence, evaluated at a class. -/
theorem coe_corrMap_add_apply (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ)
    (c₁ c₂ : Corr k X.obj.hom Y.obj.hom r) (a : W.grade X n) :
    (corrMap hA hB hC X Y r n (c₁ + c₂) a : W.H Y) =
      corrMap hA hB hC X Y r n c₁ a + corrMap hA hB hC X Y r n c₂ a := by
  rw [map_add (corrMap hA hB hC X Y r n) c₁ c₂]
  rfl

/-- Additivity of the right side of the tensor law in the first correspondence. -/
theorem pull_corrMap_add_left (X Y Y' : (SmoothProjectiveScheme k).FullSubcategory) {p : ℤ}
    (c₁ c₂ : Corr k X.obj.hom Y.obj.hom 0) (a : W.grade X p) (v : W.H Y') :
    W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p (c₁ + c₂) a) * W.pull (snd Y Y') v =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c₁ a) * W.pull (snd Y Y') v +
        W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c₂ a) * W.pull (snd Y Y') v := by
  rw [coe_corrMap_add_apply, map_add, add_mul]

/-- Additivity of the right side of the tensor law in the second correspondence. -/
theorem pull_corrMap_add_right (X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) {q : ℤ}
    (c₁ c₂ : Corr k X'.obj.hom Y'.obj.hom 0) (a' : W.grade X' q) (v : W.H Y) :
    W.pull (fst Y Y') v * W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q (c₁ + c₂) a') =
      W.pull (fst Y Y') v * W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c₁ a') +
        W.pull (fst Y Y') v * W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c₂ a') := by
  rw [coe_corrMap_add_apply, map_add, mul_add]

/-- `G` of the zero correspondence between products. -/
theorem corrMap_tensorEquiv_zero (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (r n : ℤ) :
    corrMap hA hB hC (prod X X') (prod Y Y') r n (tensorEquiv X X' Y Y' r 0) = 0 := by
  rw [LinearEquiv.map_zero]
  exact map_zero (corrMap hA hB hC (prod X X') (prod Y Y') r n)

/-- `G` is additive on correspondences between products. -/
theorem corrMap_tensorEquiv_add (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ)
    (t t' : Corr k (prodBase X.obj.hom X'.obj.hom) (prodBase Y.obj.hom Y'.obj.hom) r) :
    corrMap hA hB hC (prod X X') (prod Y Y') r n (tensorEquiv X X' Y Y' r (t + t')) =
      corrMap hA hB hC (prod X X') (prod Y Y') r n (tensorEquiv X X' Y Y' r t) +
        corrMap hA hB hC (prod X X') (prod Y Y') r n (tensorEquiv X X' Y Y' r t') := by
  rw [LinearEquiv.map_add]
  exact map_add (corrMap hA hB hC (prod X X') (prod Y Y') r n) _ _

/-- The tensor law for `c = 0`. -/
theorem corrMap_tensor_zero_left {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory} {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) (c' : Corr k X'.obj.hom Y'.obj.hom 0) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            0 c'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p 0 a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c' a') := by
  rw [LinearMap.map_zero₂ (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
      (canonicalDiagonalClassFamily k) 0 0),
    corrMap_tensorEquiv_zero hA hB hC X X' Y Y' (0 + 0) (p + q),
    LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero (corrMap hA hB hC X Y 0 p),
    LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero, zero_mul]

/-- The tensor law for `c' = 0`. -/
theorem corrMap_tensor_zero_right {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory} {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) (c : Corr k X.obj.hom Y.obj.hom 0) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c 0))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q 0 a') := by
  rw [LinearMap.map_zero (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 c),
    corrMap_tensorEquiv_zero hA hB hC X X' Y Y' (0 + 0) (p + q),
    LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero (corrMap hA hB hC X' Y' 0 q),
    LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero, mul_zero]

/-- The tensor law is additive in `c`. -/
theorem corrMap_tensor_add_left {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory} {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) {c₁ c₂ : Corr k X.obj.hom Y.obj.hom 0}
    {c' : Corr k X'.obj.hom Y'.obj.hom 0}
    (h₁ : (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c₁ c'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c₁ a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c' a'))
    (h₂ : (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c₂ c'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c₂ a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c' a')) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            (c₁ + c₂) c'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p (c₁ + c₂) a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c' a') := by
  refine (congrArg (fun t ↦ (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
      (tensorEquiv X X' Y Y' (0 + 0) t) ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ : W.H (prod
              Y Y'))) (tensor_add_left_canonical X X' Y Y' c₁ c₂ c')).trans ?_
  rw [corrMap_tensorEquiv_add hA hB hC X X' Y Y' (0 + 0) (p + q), LinearMap.add_apply,
    Submodule.coe_add]
  exact (congrArg₂ (· + ·) h₁ h₂).trans (pull_corrMap_add_left hA hB hC X Y Y' c₁ c₂ a _).symm

/-- The tensor law is additive in `c'`. -/
theorem corrMap_tensor_add_right {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory} {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) {c : Corr k X.obj.hom Y.obj.hom 0}
    {c₁ c₂ : Corr k X'.obj.hom Y'.obj.hom 0}
    (h₁ : (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c c₁))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c₁ a'))
    (h₂ : (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c c₂))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c₂ a')) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c (c₁ + c₂)))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q (c₁ + c₂) a') := by
  refine (congrArg (fun t ↦ (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
      (tensorEquiv X X' Y Y' (0 + 0) t) ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ : W.H (prod
              Y Y'))) (tensor_add_right_canonical X X' Y Y' c c₁ c₂)).trans ?_
  rw [corrMap_tensorEquiv_add hA hB hC X X' Y Y' (0 + 0) (p + q), LinearMap.add_apply,
    Submodule.coe_add]
  exact (congrArg₂ (· + ·) h₁ h₂).trans (pull_corrMap_add_right hA hB hC X' Y Y' c₁ c₂ a' _).symm

/-- The tensor law on pure blocks, read through `tensorEquiv`. -/
theorem corrMap_tensor_lofE (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) (d e d' e' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (x' : Correspondence (fieldChowSituation k) (partBase X'.obj.hom d') (partBase Y'.obj.hom e')
      e' 0) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) (DirectSum.lof ℚ ℕ _ d'
                (DirectSum.lof ℚ ℕ _ e' x'))))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _
            e' x')) a') :=
  corrMap_tensor_lof hA hB hC X X' Y Y' a a' d e d' e' x x'

/-- The tensor law, read through `tensorEquiv`. -/
theorem corrMap_tensorE (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (c : Corr k X.obj.hom Y.obj.hom 0) (c' : Corr k X'.obj.hom Y'.obj.hom 0) {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensorEquiv X X' Y Y' (0 + 0)
          (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
            c c'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c' a') := by
  induction c using Corr.induction_on with
  | zero => exact corrMap_tensor_zero_left hA hB hC a a' c'
  | add c₁ c₂ h₁ h₂ => exact corrMap_tensor_add_left hA hB hC a a' h₁ h₂
  | lof d e x =>
    induction c' using Corr.induction_on with
    | zero => exact corrMap_tensor_zero_right hA hB hC a a' _
    | add c₁ c₂ h₁ h₂ => exact corrMap_tensor_add_right hA hB hC a a' h₁ h₂
    | lof d' e' x' => exact corrMap_tensor_lofE hA hB hC X X' Y Y' a a' d e d' e' x x'

/-- **`G(c ⊗ c') ∘ κ = κ ∘ (G(c) ⊗ G(c'))`** on pure tensors, for the Künneth maps
`κ(a ⊗ a') = pr₁^*a ∪ pr₂^*a'`. -/
theorem corrMap_tensor (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (c : Corr k X.obj.hom Y.obj.hom 0) (c' : Corr k X'.obj.hom Y'.obj.hom 0) {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) :
    (corrMap hA hB hC (prod X X') (prod Y Y') (0 + 0) (p + q)
        (tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) 0 0
          c c')
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ p _ a.2) (W.pull_grade _ q _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p c a) *
        W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q c' a') :=
  corrMap_tensorE hA hB hC X X' Y Y' c c' a a'

end Stacks.WeilCohomology.WeilData

end
