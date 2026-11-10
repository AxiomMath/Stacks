module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.AssembledCap

/-!
# The assembled bivariant class and the isomorphism of Stacks 0FDZ

The last of the four parts of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`; the overview, the
implementation notes and the references for Stacks 0FDZ are at the top of its first part,
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.BaseChangePieces`.

This part assembles the bivariant class `Stacks.Chow.bivariantPieceAssembly` from a family of
classes on the pieces, packages it as the homomorphism `Stacks.Chow.bivariantPieceAssemblyHom`,
proves the two round trips `Ψ ∘ Φ = id` and `Φ ∘ Ψ = id`, and concludes with the isomorphism
`Stacks.Chow.bivariantPieceEquiv` `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})` of the tag.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section Assembly

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) {I J : Type u} (UX : I → X.Opens)
  (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))
  (hX : IsClopenDecomposition UX) (p : ℤ)

/-! ### The assembled bivariant class -/

section Assemble

variable (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp)

include hX in
/-- **Stacks 0FDZ.** The bivariant class `Ψ((c_i))` of degree `p` for `f : X ⟶ Y` assembled from
a family `(c_i)` of bivariant classes of degree `p` for the restrictions `f_i : X_i ⟶ Y_{a(i)}`:
the class whose cap operation is `Stacks.Chow.bivariantPieceAssemblyCap`.

The construction carries Stacks 02S2 and Stacks 02S1 along the legs of a cartesian square and the
three Gysin compatibilities; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`. -/
def bivariantPieceAssembly
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) :
    BivariantClass C G sX sY f hf p where
  cap g _ k := bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k
  cap_properPushforward := by
    intro T₀ T₀' g₀ _ w₀ _ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantPieceAssemblyCap_proper_naturality C G sX sY f hf UX UY a ha hX p c)
      g₀ w₀ w₀' sq₀ hfst₀ k₀ _ _ α₀
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantPieceAssemblyCap_flat_naturality C G sX sY f hf UX UY a ha hX p c)
      g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact (bivariantPieceAssemblyCap_gysin_naturality C G sX sY f hf UX UY a ha hX p hgysO hgysR
      hgysC c)
      g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-- **Stacks 0FDZ.** The assembled class caps by the assembled cap operation. -/
@[simp]
theorem bivariantPieceAssembly_cap
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    (bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c).cap
        g k α =
      bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k α :=
  rfl

/-- **Stacks 0FDZ.** The assembled class is the one the cap formula characterizes. -/
theorem isBivariantPieceAssembly_bivariantPieceAssembly
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) :
    IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p c
      (bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c) :=
  fun _ _ _ _ ↦ rfl

/-- The assembled class of `c` is any class satisfying the cap formula for `c`. -/
private theorem bivariantPieceAssembly_eq_of_isBivariantPieceAssembly
    {c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p}
    {d : BivariantClass C G sX sY f hf p}
    (h : IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p c d) :
    bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c = d :=
  eq_of_isBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
    (isBivariantPieceAssembly_bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
      hgysO hgysR hgysC c) h

/-- **Stacks 0FDZ.** Assembling is additive in the family of classes on the pieces. -/
theorem bivariantPieceAssembly_add
    (c d : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) :
    bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC
        (fun i ↦ c i + d i) =
      bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c +
        bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC d :=
  bivariantPieceAssembly_eq_of_isBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
    hgysO hgysR hgysC
    (IsBivariantPieceAssembly.add C G sX sY f hf UX UY a ha hX p
      (isBivariantPieceAssembly_bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
        hgysO hgysR hgysC c)
      (isBivariantPieceAssembly_bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
        hgysO hgysR hgysC d))

/-- **Stacks 0FDZ.** Assembling commutes with negation of the family. -/
theorem bivariantPieceAssembly_neg
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) :
    bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC
        (fun i ↦ -c i) =
      -bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c :=
  bivariantPieceAssembly_eq_of_isBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
    hgysO hgysR hgysC
    (IsBivariantPieceAssembly.neg C G sX sY f hf UX UY a ha hX p
      (isBivariantPieceAssembly_bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
        hgysO hgysR hgysC c))

/-- **Stacks 0FDZ.** The class assembled from the family of zero classes is zero. -/
theorem bivariantPieceAssembly_zero :
    bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC
        (fun _ ↦ 0) = 0 :=
  bivariantPieceAssembly_eq_of_isBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
    hgysO hgysR hgysC
    (IsBivariantPieceAssembly.zero C G sX sY f hf UX UY a ha hX p)

include hX in
/-- **Stacks 0FDZ.** The map `Ψ : ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)}) ⟶ A^p(X ⟶ Y)` of the tag, as a
homomorphism of groups. -/
def bivariantPieceAssemblyHom :
    (∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
        (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) →+
      BivariantClass C G sX sY f hf p where
  toFun c := bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c
  map_zero' :=
    bivariantPieceAssembly_zero C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC
  map_add' c d :=
    bivariantPieceAssembly_add C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c d

/-- **Stacks 0FDZ.** The map `Ψ` sends a family to the class assembled from it. -/
@[simp]
theorem bivariantPieceAssemblyHom_apply
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) :
    bivariantPieceAssemblyHom C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c =
      bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c :=
  rfl

/-! ### The isomorphism of Stacks 0FDZ -/

section Equiv

include hX in
/-- **Stacks 0FDZ, `Ψ ∘ Φ = id`.** A bivariant class for `f` is the one assembled from its
restrictions to the pieces.

On the `i`-th piece of `X ×_Y T` the assembled cap operation is the cap operation of the
restriction of `c` to the `i`-th piece, which by construction is `c ∩ -` at the test scheme
`T_{a(i)} ⟶ Y` restricted along the comparison; and `c ∩ -` commutes with restricting the test
scheme to `T_{a(i)}`, by `Stacks.Chow.BivariantClass.cap_chowGroupRestrict`. -/
theorem isBivariantPieceAssembly_bivariantPieceRestriction (c : BivariantClass C G sX sY f hf p) :
    IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
      (fun i ↦ bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c) c := by
  intro T g _ k α
  refine (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).injective
    (funext fun i ↦ ?_)
  simp only [chowGroupPullbackPieceEquiv_apply]
  have hm : g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ (UY (a i)).ι =
      (g ⁻¹ᵁ UY (a i)).ι ≫ g := Scheme.Hom.resLE_comp_ι g le_rfl
  have hmY : g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY) =
      ((g ⁻¹ᵁ UY (a i)).ι ≫ g) ≫ sY :=
    (testPiece_comp_structureMorphism C sY UY a g i).symm
  have hvY : (g ⁻¹ᵁ UY (a i)).ι ≫ (g ≫ sY) = ((g ⁻¹ᵁ UY (a i)).ι ≫ g) ≫ sY :=
    (Category.assoc _ _ _).symm
  have hv' : bivariantBaseChangeMap f g (g ⁻¹ᵁ UY (a i)).ι ≫ (pullback.fst f g ≫ sX) =
      pullback.fst f ((g ⁻¹ᵁ UY (a i)).ι ≫ g) ≫ sX := by
    rw [← Category.assoc]; simp
  have hbase := pieceComparisonCongr_comp_structureMorphism f UX UY a ha i
    (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ((g ⁻¹ᵁ UY (a i)).ι ≫ g) hm sX
  have hfactor := pieceImmersion_eq_pieceComparisonCongr_comp f UX UY a ha g i
  have hcomp : (pieceComparisonCongr f UX UY a ha i
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ((g ⁻¹ᵁ UY (a i)).ι ≫ g) hm ≫
      bivariantBaseChangeMap f g (g ⁻¹ᵁ UY (a i)).ι) ≫ (pullback.fst f g ≫ sX) =
        pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX) := by
    rw [Category.assoc, hv', hbase]
  rw [bivariantPieceAssemblyCap_restrict C G sX sY f hf UX UY a ha hX p
      (fun i ↦ bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c) g k α i,
    bivariantPieceRestriction_cap C G sX sY f hf p UX UY a ha i hgysO c
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) k _,
    bivariantPieceRestrictionCap_eq C G sX sY f hf p UX UY a ha i c
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ((g ⁻¹ᵁ UY (a i)).ι ≫ g) hm hmY
      (pieceComparisonCongr f UX UY a ha i (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
        ((g ⁻¹ᵁ UY (a i)).ι ≫ g) hm) (by simp) (by simp) k hbase,
    chowGroupCongr_chowGroupRestrict C (g ≫ sY)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
      (((g ⁻¹ᵁ UY (a i)).ι ≫ g) ≫ sY) (g ⁻¹ᵁ UY (a i)).ι
      (testPiece_comp_structureMorphism C sY UY a g i) hvY hmY k α,
    chowGroupRestrict_congr C (pullback.fst f g ≫ sX)
      (pullback.fst (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
      (pieceImmersion f UX UY a ha g i)
      (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i) (k - p) _ hfactor hcomp,
    ← chowGroupRestrict_comp C (pullback.fst f g ≫ sX)
      (pullback.fst f ((g ⁻¹ᵁ UY (a i)).ι ≫ g) ≫ sX)
      (bivariantBaseChangeMap f g (g ⁻¹ᵁ UY (a i)).ι) hv' (k - p) _ _ hbase,
    BivariantClass.cap_chowGroupRestrict C G sX sY f hf p c g (g ⁻¹ᵁ UY (a i)).ι
      ((g ⁻¹ᵁ UY (a i)).ι ≫ g) rfl (bivariantBaseChangeMap f g (g ⁻¹ᵁ UY (a i)).ι)
      (isPullback_bivariantBaseChangeMap f g (g ⁻¹ᵁ UY (a i)).ι) (by simp) k hvY hv' α]

include hX in
/-- **Stacks 0FDZ, `Φ ∘ Ψ = id`.** The restriction to the `i`-th piece of the class assembled
from a family `(c_i)` is `c_i`.

This is the "immediate" direction of the source: by
`Stacks.Chow.bivariantPieceAssemblyCap_restrict` the assembled cap operation restricted to the
`i`-th piece of `X ×_Y (T ⟶ Y_{a(i)} ⟶ Y)` is `c_i ∩ -`, and the piece of the test scheme over
`Y_{a(i)}` is the whole of it, so the two presentations of the `i`-th piece differ by an
isomorphism over the test scheme. -/
theorem bivariantPieceRestriction_bivariantPieceAssembly
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) (i : I) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO
        (bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c) =
      c i := by
  refine BivariantClass.ext C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
    (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p ?_
  intro T' g' _ k β
  have hTop : ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
    rfl
  have hiso : IsIso (((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι) := by
    rw [hTop]
    exact inferInstanceAs (IsIso (Scheme.topIso T').hom)
  have hm : ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι ≫ g' =
      (g' ≫ (UY (a i)).ι).resLE (UY (a i)) ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl := by
    rw [← cancel_mono (UY (a i)).ι, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hqY : ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι ≫ (g' ≫ ((UY (a i)).ι ≫ sY)) =
      (g' ≫ (UY (a i)).ι).resLE (UY (a i)) ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl ≫
        ((UY (a i)).ι ≫ sY) := by
    rw [← Category.assoc, hm]
  have hgY : g' ≫ ((UY (a i)).ι ≫ sY) = (g' ≫ (UY (a i)).ι) ≫ sY :=
    (Category.assoc g' (UY (a i)).ι sY).symm
  -- the two presentations of the `i`-th piece of the base change
  have hrng : (pieceComparison f UX UY a ha i g').opensRange =
      (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i).opensRange :=
    (opensRange_pieceComparison f UX UY a ha i g').trans
      (opensRange_pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i).symm
  have hρ := isoOfOpensRangeEq_hom_fac (pieceComparison f UX UY a ha i g')
    (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng
  have hρinv := isoOfOpensRangeEq_inv_fac (pieceComparison f UX UY a ha i g')
    (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng
  have hfst : (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
        (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv ≫
      pullback.fst (pieceMap f UX UY a ha i) g' =
        pullback.fst (pieceMap f UX UY a ha i)
          ((g' ≫ (UY (a i)).ι).resLE (UY (a i))
            ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl) := by
    rw [← cancel_mono (UX i).ι, Category.assoc,
      ← opensPullbackComparison_fst f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
        (pieceMap_comp_ι f UX UY a ha i) g',
      ← pieceImmersion_comp_fst f UX UY a ha (g' ≫ (UY (a i)).ι) i, ← Category.assoc, hρinv]
  have hsnd : pullback.snd (pieceMap f UX UY a ha i)
        ((g' ≫ (UY (a i)).ι).resLE (UY (a i))
          ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl) ≫
      ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι =
        (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
            (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv ≫
          pullback.snd (pieceMap f UX UY a ha i) g' := by
    rw [← pieceImmersion_comp_snd f UX UY a ha (g' ≫ (UY (a i)).ι) i,
      ← opensPullbackComparison_snd f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
        (pieceMap_comp_ι f UX UY a ha i) g', ← Category.assoc, hρinv]
  have hρbase : (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
        (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv ≫
      (pullback.fst (pieceMap f UX UY a ha i) g' ≫ ((UX i).ι ≫ sX)) =
        pullback.fst (pieceMap f UX UY a ha i)
            ((g' ≫ (UY (a i)).ι).resLE (UY (a i))
              ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX) := by
    rw [← Category.assoc, hfst]
  have hρhombase : (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
        (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).hom ≫
      (pullback.fst (pieceMap f UX UY a ha i)
          ((g' ≫ (UY (a i)).ι).resLE (UY (a i))
            ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) =
        pullback.fst (pieceMap f UX UY a ha i) g' ≫ ((UX i).ι ≫ sX) := by
    rw [← hfst]
    simp
  have hfacq := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
    ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι hqY k
  have hfacρ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
    (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
      (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv hρbase (k - p)
  rw [bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply,
    bivariantPieceAssembly_cap,
    chowGroupRestrict_congr C (pullback.fst f (g' ≫ (UY (a i)).ι) ≫ sX)
      (pullback.fst (pieceMap f UX UY a ha i) g' ≫ ((UX i).ι ≫ sX))
      (pieceComparison f UX UY a ha i g')
      (pieceComparison_comp_structureMorphism f UX UY a ha i g' sX) (k - p) _ hρ.symm
      (by rw [Category.assoc, pieceImmersion_comp_structureMorphism, hρhombase]),
    ← chowGroupRestrict_comp C (pullback.fst f (g' ≫ (UY (a i)).ι) ≫ sX) _
      (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i)
      (pieceImmersion_comp_structureMorphism C sX f UX UY a ha (g' ≫ (UY (a i)).ι) i) (k - p) _ _
      hρhombase,
    bivariantPieceAssemblyCap_restrict C G sX sY f hf UX UY a ha hX p c (g' ≫ (UY (a i)).ι) k _ i,
    chowGroupRestrict_chowGroupCongr C (g' ≫ ((UY (a i)).ι ≫ sY)) ((g' ≫ (UY (a i)).ι) ≫ sY) _
      ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι hqY
      (testPiece_comp_structureMorphism C sY UY a (g' ≫ (UY (a i)).ι) i) hgY k β,
    chowGroupRestrict_eq_chowPushforwardOfIso_of_comp_id C _ _ _ hρhombase
      (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
        (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv hρbase
      (Iso.hom_inv_id _) (k - p),
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _
      (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
        (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv hρbase (k - p) hfacρ,
    ← BivariantClass.proper_naturality_of_eq C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p (c i) g'
      ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι
      ((g' ≫ (UY (a i)).ι).resLE (UY (a i)) ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)) le_rfl) hm
      (isoOfOpensRangeEq (pieceComparison f UX UY a ha i g')
        (pieceImmersion f UX UY a ha (g' ≫ (UY (a i)).ι) i) hrng).inv
      (IsPullback.of_vert_isIso (CommSq.mk hsnd)) hfst k hqY hfacq hfacρ _,
    properChowPushforward_eq_chowPushforwardOfIso C _ _
      ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι hqY k hfacq,
    ← eq_chowPushforwardOfIso_chowGroupRestrict C (g' ≫ ((UY (a i)).ι ≫ sY)) _
      ((g' ≫ (UY (a i)).ι) ⁻¹ᵁ UY (a i)).ι hqY k β]

/-- **Stacks 0FDZ.** `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})`: a bivariant class of degree
`p` for `f : X ⟶ Y` is the same thing as a family of bivariant classes of degree `p` for the
restrictions `f_i : X_i ⟶ Y_{a(i)}`.

The forward map `Φ` is restriction to the pieces,
`Stacks.Chow.bivariantPieceRestrictionHom`, and the inverse `Ψ` is assembling,
`Stacks.Chow.bivariantPieceAssemblyHom`. The two round trips are
`Stacks.Chow.isBivariantPieceAssembly_bivariantPieceRestriction` together with
`Stacks.Chow.eq_of_isBivariantPieceAssembly`, and
`Stacks.Chow.bivariantPieceRestriction_bivariantPieceAssembly`.

The construction carries only the three Gysin compatibilities of a `Stacks.Chow.GysinSystem`
beyond the hypotheses of `Stacks.Chow.bivariantPieceRestriction`: `hgysO`, the open-immersion
case of Stacks 02TA, together with `hgysR` and `hgysC`. All three are discharged at the Gysin
system of the genuine first Chern class rule, so **no `@[stacks 0FDZ]` attribute is placed here**:
the tag sits on `Stacks.Chow.bivariantPieceEquivOfInvertible`
(`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible`), which is
this isomorphism at that system. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`. Stacks 02S1 and Stacks
02S2, both for a general flat or proper morphism and along the legs of a cartesian square, are no
longer among the hypotheses: they are the theorems
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`,
`Stacks.Chow.flatPullbackFactorsOnPieces`,
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence` and
`Stacks.Chow.properPushforwardFactorsOnPieces`. -/
def bivariantPieceEquiv :
    BivariantClass C G sX sY f hf p ≃+
      ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY) (pieceMap f UX UY a ha i)
        (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p where
  toFun := bivariantPieceRestrictionHom C G sX sY f hf p UX UY a ha hgysO
  invFun := bivariantPieceAssemblyHom C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC
  left_inv c :=
    (eq_of_isBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
      (isBivariantPieceAssembly_bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
        hgysO hgysR hgysC
        (fun i ↦ bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c))
      (isBivariantPieceAssembly_bivariantPieceRestriction C G sX sY f hf UX UY a ha hX p hgysO
        c))
  right_inv c :=
    funext fun i ↦ bivariantPieceRestriction_bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p
      hgysO hgysR hgysC c i
  map_add' := (bivariantPieceRestrictionHom C G sX sY f hf p UX UY a ha hgysO).map_add

/-- **Stacks 0FDZ.** The isomorphism of the tag is restriction to the pieces. -/
@[simp]
theorem bivariantPieceEquiv_apply (c : BivariantClass C G sX sY f hf p) (i : I) :
    bivariantPieceEquiv C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c i =
      bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c :=
  rfl

/-- **Stacks 0FDZ.** The inverse of the isomorphism of the tag is assembling. -/
@[simp]
theorem bivariantPieceEquiv_symm_apply
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p) :
    (bivariantPieceEquiv C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC).symm c =
      bivariantPieceAssembly C G sX sY f hf UX UY a ha hX p hgysO hgysR hgysC c :=
  rfl

end Equiv

end Assemble

end Assembly

end Stacks.Chow

end
