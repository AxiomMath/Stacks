module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.ZeroSchemePieces

/-!
# The cap operation assembled from classes on the pieces, and its three axioms

The third of the four parts of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`; the overview, the
implementation notes and the references for Stacks 0FDZ are at the top of its first part,
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.BaseChangePieces`.

Given a family `(c_i)` of bivariant classes for the restrictions `f_i : X_i ⟶ Y_{a(i)}`, this part
builds the assembled cap operation `Stacks.Chow.bivariantPieceAssemblyCap`, proves it additive in
the family, characterizes the assembled class (`Stacks.Chow.IsBivariantPieceAssembly`), and proves
the proper-pushforward, the flat-pullback and the Gysin axiom of Stacks 0B76 for it
(`Stacks.Chow.bivariantPieceAssemblyCap_proper_naturality`,
`Stacks.Chow.bivariantPieceAssemblyCap_flat_naturality`,
`Stacks.Chow.bivariantPieceAssemblyCap_gysin_naturality`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The cap operation assembled from a family of classes on the pieces -/

/-- The restriction of a test morphism `h` to the pieces is a morphism over the base. -/
private theorem testPieceMap_comp_structureMorphism {Y Z : Scheme.{u}} {I J : Type u}
    (UY : J → Y.Opens) (a : I → J) {T T' : Scheme.{u}}
    (g : T ⟶ Y) (h : T' ⟶ T) (i : I) (q : (UY (a i) : Scheme.{u}) ⟶ Z) :
    testPieceMap UY a g h i ≫ (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ q) =
      (h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫ q := by
  rw [← Category.assoc, testPieceMap_comp_resLE]

/-- The induced map of the pieces of the base changes is a morphism over the base. -/
private theorem piecePullbackMap_comp_structureMorphism {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
    (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) {T T' : Scheme.{u}} (g : T ⟶ Y) (h : T' ⟶ T)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (i : I) (q : X ⟶ Z) :
    piecePullbackMap f UX UY a ha g h h' hfst i ≫
      (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ q)) =
        pullback.fst (pieceMap f UX UY a ha i)
          ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ q) := by
  rw [← Category.assoc, piecePullbackMap_comp_fst]

section Assembly

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) {I J : Type u} (UX : I → X.Opens)
  (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))
  (hX : IsClopenDecomposition UX) (p : ℤ)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
include hf in
/-- The restriction `f_i : X_i ⟶ Y_{a(i)}` of `f` to a piece is a morphism over the base, the
structure morphisms of the pieces being taken through their inclusions. -/
alias pieceMap_comp_pieceStructureMorphism := pieceMap_comp_structureMorphism

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
/-- The inclusion of the piece `T_{a(i)} = g^{-1}(Y_{a(i)})` of a test scheme is a morphism over
the base, the structure morphism of the piece being read through the restricted test morphism
`T_{a(i)} ⟶ Y_{a(i)}`. -/
theorem testPiece_comp_structureMorphism {T : Scheme.{u}} (g : T ⟶ Y) (i : I) :
    (g ⁻¹ᵁ UY (a i)).ι ≫ (g ≫ sY) =
      g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY) := by
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι g (le_rfl : g ⁻¹ᵁ UY (a i) ≤ _),
    Category.assoc]

include hX in
/-- **Stacks 0FDZ.** The cap operation assembled from a family `(c_i)` of bivariant classes of
degree `p` for the restrictions `f_i : X_i ⟶ Y_{a(i)}`: on a test scheme `g : T ⟶ Y` it sends
`α ∈ A_k(T)` to the unique class in `A_{k-p}(X ×_Y T)` whose restriction to the `i`-th piece
`X_i ×_{Y_{a(i)}} T_{a(i)}` is `c_i ∩ α|_{T_{a(i)}}`.

It is well defined because the Chow groups of `X ×_Y T` decompose along those pieces, by
`Stacks.Chow.chowGroupPullbackPieceEquiv`. -/
@[stacks 0FDZ "the cap operation assembled from a family of bivariant classes on the pieces"]
def bivariantPieceAssemblyCap
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - p) :=
  (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).symm.toAddMonoidHom.comp
    (AddMonoidHom.pi fun i ↦
      ((c i).cap (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) k).comp
        (chowGroupRestrict C (g ≫ sY)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
          (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) k))

/-- **The characterizing property of the assembled cap operation.** Its restriction along the
`i`-th piece immersion is the cap product of `c_i` with the restriction of the class to the piece
`T_{a(i)}` of the test scheme. -/
theorem bivariantPieceAssemblyCap_restrict
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) (i : I) :
    chowGroupRestrict C (pullback.fst f g ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
        (pieceImmersion f UX UY a ha g i)
        (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i) (k - p)
        (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k α) =
      (c i).cap (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) k
        (chowGroupRestrict C (g ≫ sY)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
          (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) k α) := by
  rw [← chowGroupPullbackPieceEquiv_apply C sX f UX UY a ha hX g (k - p)]
  exact congrFun ((chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).apply_symm_apply _) i

/-! ### Additivity of the assembled cap operation in the family of classes -/

/-- Assembling is additive in the family of classes on the pieces: the cap operation assembled
from `(c_i + d_i)` is the sum of the two assembled operations. -/
theorem bivariantPieceAssemblyCap_add
    (c d : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p (fun i ↦ c i + d i) g k α =
      bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k α +
        bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p d g k α := by
  refine (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).injective
    (funext fun i ↦ ?_)
  simp only [chowGroupPullbackPieceEquiv_apply, map_add, bivariantPieceAssemblyCap_restrict,
    BivariantClass.add_cap]

/-- Assembling commutes with negation of the family of classes on the pieces. -/
theorem bivariantPieceAssemblyCap_neg
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p (fun i ↦ -c i) g k α =
      -bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k α := by
  refine (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).injective
    (funext fun i ↦ ?_)
  simp only [chowGroupPullbackPieceEquiv_apply, map_neg, bivariantPieceAssemblyCap_restrict,
    BivariantClass.neg_cap]

/-- The cap operation assembled from the family of zero classes is zero. -/
theorem bivariantPieceAssemblyCap_zero {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p (fun _ ↦ 0) g k α = 0 := by
  refine (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).injective
    (funext fun i ↦ ?_)
  simp only [chowGroupPullbackPieceEquiv_apply, map_zero, bivariantPieceAssemblyCap_restrict,
    BivariantClass.zero_cap]

/-! ### The characterization of the assembled class -/

/-- The assertion that a bivariant class of degree `p` for `f : X ⟶ Y` is the one assembled from
the family `(c_i)` on the pieces, namely that it caps by
`Stacks.Chow.bivariantPieceAssemblyCap`.

This is the property the map `Ψ` of Stacks 0FDZ is defined by, and
`Stacks.Chow.eq_of_isBivariantPieceAssembly` shows it determines the class. -/
def IsBivariantPieceAssembly
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    (c' : BivariantClass C G sX sY f hf p) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k),
    c'.cap g k α = bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k α

/-- **Stacks 0FDZ.** The cap formula determines the assembled class: two bivariant classes
assembled from the same family on the pieces are equal. With
`Stacks.Chow.chowGroupPullbackPieceEquiv` this is the injectivity of the map `Ψ` of the tag. -/
theorem eq_of_isBivariantPieceAssembly
    {c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p}
    {c' d' : BivariantClass C G sX sY f hf p}
    (hc' : IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p c c')
    (hd' : IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p c d') : c' = d' := by
  refine BivariantClass.ext C G sX sY f hf p ?_
  intro T g _ k α
  rw [hc' g k α, hd' g k α]

namespace IsBivariantPieceAssembly

/-- Assembling is additive: the class assembled from a sum of families is the sum of the assembled
classes. -/
theorem add
    {c d : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p}
    {c' d' : BivariantClass C G sX sY f hf p}
    (hc : IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p c c')
    (hd : IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p d d') :
    IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p (fun i ↦ c i + d i) (c' + d') := by
  intro T g _ k α
  rw [BivariantClass.add_cap, hc g k α, hd g k α, bivariantPieceAssemblyCap_add]

/-- Assembling commutes with negation. -/
theorem neg
    {c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p}
    {c' : BivariantClass C G sX sY f hf p}
    (hc : IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p c c') :
    IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p (fun i ↦ -c i) (-c') := by
  intro T g _ k α
  rw [BivariantClass.neg_cap, hc g k α, bivariantPieceAssemblyCap_neg]

/-- The class assembled from the family of zero classes is zero. -/
theorem zero :
    IsBivariantPieceAssembly C G sX sY f hf UX UY a ha hX p (fun _ ↦ 0) 0 := by
  intro T g _ k α
  rw [BivariantClass.zero_cap, bivariantPieceAssemblyCap_zero]

end IsBivariantPieceAssembly

/-! ### The proper-pushforward axiom of the assembled cap operation -/

include hX in
/-- **Stacks 0FDZ.** The assembled cap operation commutes with proper pushforward: the
proper-pushforward axiom of Stacks 0B76 for `Stacks.Chow.bivariantPieceAssemblyCap`.

Both sides are determined by their restrictions to the pieces of `X ×_Y T`, and on the `i`-th
piece the identity is the proper axiom of `c_i` for the restriction of `h` to the pieces, the
restrictions being moved past the two proper pushforwards by the open-immersion case of
Stacks 02RG. -/
theorem bivariantPieceAssemblyCap_proper_naturality
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((h ≫ g) ≫ sY) k),
      bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k
          (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k
            hfac α) =
        properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - p) hfac'
          (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c (h ≫ g) k α) := by
  intro hfac hfac' α
  have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  refine (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g (k - p)).injective
    (funext fun i ↦ ?_)
  simp only [chowGroupPullbackPieceEquiv_apply]
  have : IsProper (testPieceMap UY a g h i) :=
    isProper_of_isPullback h ((h ≫ g) ⁻¹ᵁ UY (a i)).ι (g ⁻¹ᵁ UY (a i)).ι
      (testPieceMap UY a g h i) (isPullback_testPieceMap UY a g h i)
  have : IsProper (piecePullbackMap f UX UY a ha g h h' hfst i) :=
    isProper_of_isPullback h' (pieceImmersion f UX UY a ha (h ≫ g) i)
      (pieceImmersion f UX UY a ha g i) (piecePullbackMap f UX UY a ha g h h' hfst i)
      (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i)
  have hqt := testPieceMap_comp_structureMorphism UY a g h i ((UY (a i)).ι ≫ sY)
  have hqp := piecePullbackMap_comp_structureMorphism f UX UY a ha g h h' hfst i sX
  have hfacA := properPushforwardFactorsOnPieces C ((h ≫ g) ≫ sY) (g ≫ sY) _ _ h
    (by simp [Category.assoc])
    ((h ≫ g) ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a (h ≫ g) i)
    (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i)
    (testPieceMap UY a g h i) hqt (isPullback_testPieceMap UY a g h i) k hfac
  have hfacB := properPushforwardFactorsOnPieces C
    (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) _ _ h'
    (by rw [← Category.assoc, hfst]) (pieceImmersion f UX UY a ha (h ≫ g) i)
    (pieceImmersion_comp_structureMorphism C sX f UX UY a ha (h ≫ g) i)
    (pieceImmersion f UX UY a ha g i)
    (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i)
    (piecePullbackMap f UX UY a ha g h h' hfst i) hqp
    (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i) (k - p) hfac'
  rw [bivariantPieceAssemblyCap_restrict,
    chowGroupRestrict_properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) _ _ h
      (by simp [Category.assoc]) _ (testPiece_comp_structureMorphism C sY UY a (h ≫ g) i) _
      (testPiece_comp_structureMorphism C sY UY a g i) (testPieceMap UY a g h i) hqt
      (isPullback_testPieceMap UY a g h i) k hfac hfacA,
    BivariantClass.proper_naturality_of_eq C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p (c i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
      (testPieceMap UY a g h i)
      ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl)
      (testPieceMap_comp_resLE UY a g h i) (piecePullbackMap f UX UY a ha g h h' hfst i)
      (isPullback_piecePullbackMap_snd f UX UY a ha g h h' hfst sq.w i)
      (piecePullbackMap_comp_fst f UX UY a ha g h h' hfst i) k hqt hfacA hfacB,
    chowGroupRestrict_properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX)
      (pullback.fst f g ≫ sX) _ _ h' (by rw [← Category.assoc, hfst]) _
      (pieceImmersion_comp_structureMorphism C sX f UX UY a ha (h ≫ g) i) _
      (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i)
      (piecePullbackMap f UX UY a ha g h h' hfst i) hqp
      (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i) (k - p) hfac' hfacB,
    bivariantPieceAssemblyCap_restrict]

/-! ### The flat-pullback axiom of the assembled cap operation -/

include hX in
/-- **Stacks 0FDZ.** The assembled cap operation commutes with flat pullback of fixed relative
dimension: the flat naturality axiom of Stacks 0B76 for
`Stacks.Chow.bivariantPieceAssemblyCap`.

As in `Stacks.Chow.BivariantClass`, the degrees are `(k + r) - p` on one side and `(k - p) + r`
on the other — the same integer written two ways — so the conclusion is an `HEq`. Both sides are
determined by their restrictions to the pieces of `X ×_Y T`, and on the `i`-th piece the identity
is the flat axiom of `c_i` for the restriction of `h` to the pieces. -/
theorem bivariantPieceAssemblyCap_flat_naturality
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (g ≫ sY) k),
      HEq
        (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c (h ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
          (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g k α)) := by
  have hft' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hfl' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  intro hr' hfac hfac' α
  have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
  refine heq_of_injective_heq
    (fun n x ↦ chowGroupPullbackPieceEquiv C sX f UX UY a ha hX (h ≫ g) n x)
    (fun n ↦ (chowGroupPullbackPieceEquiv C sX f UX UY a ha hX (h ≫ g) n).injective) hidx ?_
  refine heq_pi_of_heq (K := I) (A := fun n i ↦ chowGroup C
      (pullback.fst (pieceMap f UX UY a ha i)
        ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) n)
    hidx fun i ↦ ?_
  have hftt : LocallyOfFiniteType (testPieceMap UY a g h i) :=
    MorphismProperty.of_isPullback (isPullback_testPieceMap UY a g h i)
      (P := @LocallyOfFiniteType) inferInstance
  have hflt : Flat (testPieceMap UY a g h i) :=
    MorphismProperty.of_isPullback (isPullback_testPieceMap UY a g h i) (P := @Flat)
      inferInstance
  have hftp : LocallyOfFiniteType (piecePullbackMap f UX UY a ha g h h' hfst i) :=
    MorphismProperty.of_isPullback (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i)
      (P := @LocallyOfFiniteType) inferInstance
  have hflp : Flat (piecePullbackMap f UX UY a ha g h h' hfst i) :=
    MorphismProperty.of_isPullback (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i)
      (P := @Flat) inferInstance
  have hrt : AlgebraicGeometry.RelativeDimension (testPieceMap UY a g h i) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_testPieceMap UY a g h i) hr
  have hrp : AlgebraicGeometry.RelativeDimension
      (piecePullbackMap f UX UY a ha g h h' hfst i) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i) hr'
  have hqt := testPieceMap_comp_structureMorphism UY a g h i ((UY (a i)).ι ≫ sY)
  have hqp := piecePullbackMap_comp_structureMorphism f UX UY a ha g h h' hfst i sX
  have hfacA := flatPullbackFactorsOnPieces C ((h ≫ g) ≫ sY) (g ≫ sY) _ _ h
    (by simp [Category.assoc]) r hr
    ((h ≫ g) ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a (h ≫ g) i)
    (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i)
    (testPieceMap UY a g h i) hqt (isPullback_testPieceMap UY a g h i) k hrt hfac
  have hfacB := flatPullbackFactorsOnPieces C (pullback.fst f (h ≫ g) ≫ sX)
    (pullback.fst f g ≫ sX) _ _ h'
    (by rw [← Category.assoc, hfst]) r hr' (pieceImmersion f UX UY a ha (h ≫ g) i)
    (pieceImmersion_comp_structureMorphism C sX f UX UY a ha (h ≫ g) i)
    (pieceImmersion f UX UY a ha g i)
    (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i)
    (piecePullbackMap f UX UY a ha g h h' hfst i) hqp
    (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i) (k - p) hrp hfac'
  have hL := bivariantPieceAssemblyCap_restrict C G sX sY f hf UX UY a ha hX p c (h ≫ g)
    (k + (r : ℤ)) (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r
      hr k hfac α) i
  have hR := bivariantPieceAssemblyCap_restrict C G sX sY f hf UX UY a ha hX p c g k α i
  simp only [chowGroupPullbackPieceEquiv_apply]
  rw [hL, chowGroupRestrict_flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) _ _ h
      (by simp [Category.assoc]) r hr _ (testPiece_comp_structureMorphism C sY UY a (h ≫ g) i) _
      (testPiece_comp_structureMorphism C sY UY a g i) (testPieceMap UY a g h i) hqt
      (isPullback_testPieceMap UY a g h i) hrt k hfac hfacA,
    chowGroupRestrict_flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX)
      (pullback.fst f g ≫ sX) _ _ h' (by rw [← Category.assoc, hfst]) r hr' _
      (pieceImmersion_comp_structureMorphism C sX f UX UY a ha (h ≫ g) i) _
      (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i)
      (piecePullbackMap f UX UY a ha g h h' hfst i) hqp
      (isPullback_piecePullbackMap f UX UY a ha g h h' hfst i) hrp (k - p) hfac' hfacB,
    hR]
  exact BivariantClass.flat_naturality_of_eq C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
    (pieceMap f UX UY a ha i)
    (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p (c i)
    (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) (testPieceMap UY a g h i)
    ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl)
    (testPieceMap_comp_resLE UY a g h i) r hrt
    (piecePullbackMap f UX UY a ha g h h' hfst i)
    (isPullback_piecePullbackMap_snd f UX UY a ha g h h' hfst sq.w i)
    (piecePullbackMap_comp_fst f UX UY a ha g h h' hfst i) k hqt hrp hfacA hfacB _

/-! ### The Gysin axiom of the assembled cap operation -/

include hX in
/-- **Stacks 0FDZ.** The assembled cap operation commutes with the Gysin map of the zero scheme
of a section of an invertible module on a test scheme: the Gysin axiom of Stacks 0B76 for
`Stacks.Chow.bivariantPieceAssemblyCap`.

Both sides are determined by their restrictions to the pieces of the zero scheme of the
pulled-back section, by `Stacks.Chow.chowGroupZeroSchemePieceEquiv`. On the `i`-th piece the
identity is the Gysin axiom of `c_i` at the test scheme `T_{a(i)}` carrying the module pulled
back along the inclusion of `T_{a(i)}`: the restriction is moved past the Gysin map on the test
scheme by `Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction` and past the Gysin map on the
base change by `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`, the two invertible modules
on the piece are reconciled by `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackComp`, and the two
presentations of the `i`-th piece of the zero scheme downstairs are identified by
`Stacks.Chow.zeroSchemeTestPieceIso`. -/
theorem bivariantPieceAssemblyCap_gysin_naturality
    (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
    (hgysC : G.IsNaturalUnderPullbackComp)
    (c : ∀ i, BivariantClass C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s
    let E := Stacks.Divisors.zeroScheme (pullback f g) L' s'
    ∀ (e : pullback f (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f g ≫ sX) =
        pullback.fst f (D.subschemeι ≫ g) ≫ sX)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst f (D.subschemeι ≫ g) ≫ sX) (E.subschemeι ≫ pullback.fst f g ≫ sX)
        e.hom hbase (k - p))
      (α : chowGroup C (g ≫ sY) (k + 1)),
      properChowPushforward C (pullback.fst f (D.subschemeι ≫ g) ≫ sX)
          (E.subschemeι ≫ pullback.fst f g ≫ sX) e.hom hbase (k - p) hfac
          (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c (D.subschemeι ≫ g) k
            (G.onChow (g ≫ sY) L s k α)) =
        G.onChow (pullback.fst f g ≫ sX) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
            (by omega : (k + 1) - p = (k - p) + 1))
            (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g (k + 1) α)) := by
  dsimp only
  intro e he hbase hfac α
  have hidx : (k + 1) - p = (k - p) + 1 := by omega
  refine (chowGroupZeroSchemePieceEquiv C sX f UX UY a ha hX g L s (k - p)).injective
    (funext fun i ↦ ?_)
  simp only [chowGroupZeroSchemePieceEquiv_apply]
  -- the structure morphisms of the pieces, of the test scheme and of the zero schemes
  have hPI : pieceImmersion f UX UY a ha g i ≫ (pullback.fst f g ≫ sX) =
      pullback.fst (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
        ((UX i).ι ≫ sX) :=
    pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i
  have hqB : pullback.snd f g ≫ (g ≫ sY) = pullback.fst f g ≫ sX :=
    pullbackSnd_comp_structureMorphism_eq C sX sY f hf g
  have hqA : pieceTestProjection f UX UY a ha g i ≫ (g ≫ sY) =
      pullback.fst (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
        ((UX i).ι ≫ sX) := by
    rw [Category.assoc, testPiece_comp_structureMorphism,
      pullbackSnd_comp_structureMorphism_eq C ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
        (pieceMap f UX UY a ha i)
        (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)]
  have hJJ := zeroSchemePieceImmersion_comp_structureMorphism C sX f UX UY a ha g L s i
  have hmA := pieceImmersion_comp_structureMorphism C sX f UX UY a ha
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i
  -- the cartesian square cutting the `i`-th piece out of the base change of the zero scheme
  have hcomm : (zeroSchemePieceComparison f UX UY a ha g L s i).hom ≫
      zeroSchemePieceImmersion f UX UY a ha g L s i =
        pieceImmersion f UX UY a ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i ≫
          e.hom := by
    rw [← cancel_mono (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι,
      Category.assoc, Category.assoc, he]
    exact zeroSchemePieceComparison_hom_comp f UX UY a ha g L s i
  have hrange : e.hom ⁻¹ᵁ (zeroSchemePieceImmersion f UX UY a ha g L s i).opensRange =
      (pieceImmersion f UX UY a ha
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i).opensRange := by
    rw [opensRange_zeroSchemePieceImmersion, opensRange_pieceImmersion,
      ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, he]
    simp only [pullbackMap_fst, Category.comp_id]
  have hsq : IsPullback
      (pieceImmersion f UX UY a ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i)
      (zeroSchemePieceComparison f UX UY a ha g L s i).hom e.hom
      (zeroSchemePieceImmersion f UX UY a ha g L s i) :=
    (AlgebraicGeometry.IsOpenImmersion.isPullback
      (zeroSchemePieceComparison f UX UY a ha g L s i).hom
      (pieceImmersion f UX UY a ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i)
      (zeroSchemePieceImmersion f UX UY a ha g L s i) e.hom hcomm.symm hrange).flip
  have hq' : (zeroSchemePieceComparison f UX UY a ha g L s i).hom ≫
      ((zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))) =
      pullback.fst (pieceMap f UX UY a ha i)
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫
        ((UX i).ι ≫ sX) := by
    rw [← hJJ, ← Category.assoc, hcomm, Category.assoc, hbase, hmA]
  have hfac' := properPushforwardFactorsOnPieces C _ _ _ _ e.hom hbase
    (pieceImmersion f UX UY a ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i) hmA
    (zeroSchemePieceImmersion f UX UY a ha g L s i) hJJ
    (zeroSchemePieceComparison f UX UY a ha g L s i).hom hq' hsq (k - p) hfac
  -- the left-hand side, restricted to the `i`-th piece
  have hL := chowGroupRestrict_properChowPushforward C _ _ _ _ e.hom hbase
    (pieceImmersion f UX UY a ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i) hmA
    (zeroSchemePieceImmersion f UX UY a ha g L s i) hJJ
    (zeroSchemePieceComparison f UX UY a ha g L s i).hom hq' hsq (k - p) hfac hfac'
    (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k (G.onChow (g ≫ sY) L s k α))
  -- the right-hand side, restricted to the `i`-th piece
  have hRgysO := GysinSystem.onChow_openImmersion hgysO (g ≫ sY)
    (pieceTestProjection f UX UY a ha g i) (pullback.snd f g)
    (pullback.fst (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
    (pullback.fst f g ≫ sX) hqA hqB (pieceImmersion f UX UY a ha g i)
    (pieceImmersion_comp_snd f UX UY a ha g i) L s (k - p)
    (zeroSchemePieceImmersion f UX UY a ha g L s i)
    (zeroSchemePieceImmersion_comp_subschemeι f UX UY a ha g L s i) hJJ hPI
    (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX)) hidx)
      (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g (k + 1) α))
  have hcast := chowGroupRestrict_cast C (pullback.fst f g ≫ sX)
    (pullback.fst (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
    (pieceImmersion f UX UY a ha g i) hPI hidx
    (bivariantPieceAssemblyCap C G sX sY f hf UX UY a ha hX p c g (k + 1) α)
  -- the two invertible modules on the `i`-th piece
  have hC := hgysC (pullback.fst (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
    (pullback.snd (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
    (g ⁻¹ᵁ UY (a i)).ι L s (k - p)
    (Eq.mp (congrArg (chowGroup C (pullback.fst (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))) hidx)
      ((c i).cap (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) (k + 1)
        (chowGroupRestrict C (g ≫ sY)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
          (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) (k + 1) α)))
  -- the Gysin axiom of `c_i` at the test scheme `T_{a(i)}`
  have hbcmfst : bivariantBaseChangeMap (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
        (zeroSchemeTestPiece UY a g L s i).subschemeι ≫
      pullback.fst (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) =
        pullback.fst (pieceMap f UX UY a ha i)
          ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
            g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) := by
    simp only [pullbackMap_fst, Category.comp_id]
  have hei := zeroSchemeBaseChangeIso_hom_subschemeι (pieceMap f UX UY a ha i)
    (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
    ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)
  have hbasei : (zeroSchemeBaseChangeIso (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
        ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)).hom ≫
      ((Stacks.Divisors.zeroScheme
          (pullback (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
          ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))).obj
            ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L))
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (pieceMap f UX UY a ha i)
              (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
            ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s))).subschemeι ≫
        pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY a ha i)
          ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
            g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX) := by
    rw [reassoc_of% hei, reassoc_of% hbcmfst]
  have hfaci := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
    (zeroSchemeBaseChangeIso (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
      ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)).hom hbasei (k - p)
  have hci := (c i).gysin_naturality (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
    ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s) k
    (zeroSchemeBaseChangeIso (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
      ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)) hei hbasei hfaci
    (chowGroupRestrict C (g ≫ sY)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
      (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) (k + 1) α)
  -- the Gysin map on the test scheme restricted to the `i`-th piece of `Z(s)`
  have hjD : zeroSchemeOpensRestrictMap (g ⁻¹ᵁ UY (a i)).ι L s ≫
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY)) =
        (zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY)) := by
    rw [← Category.assoc, zeroSchemeOpensRestrictMap_comp_subschemeι, Category.assoc,
      testPiece_comp_structureMorphism]
  have hR := hgysR (g ≫ sY)
    (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
    (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) L s k
    (zeroSchemeOpensRestrictMap (g ⁻¹ᵁ UY (a i)).ι L s)
    (zeroSchemeOpensRestrictMap_comp_subschemeι (g ⁻¹ᵁ UY (a i)).ι L s) hjD α
  have hκY : (zeroSchemeTestPieceIso UY a g L s i).hom ≫
      ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))) =
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY) :=
    zeroSchemeTestPieceIso_hom_comp_resLE_assoc UY a g L s i ((UY (a i)).ι ≫ sY)
  have hκYL : (zeroSchemeTestPieceIso UY a g L s i).hom ≫
      (((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
        g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UY (a i)).ι ≫ sY)) =
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY) := hκY
  have hfacκ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
    (zeroSchemeTestPieceIso UY a g L s i).hom hκYL k
  have hTPr : (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι ≫
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ (g ≫ sY)) =
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY) :=
    testPiece_comp_structureMorphism C sY UY a
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i
  have hδ : chowGroupRestrict C _ _ (zeroSchemeTestPieceIso UY a g L s i).hom hκY k
        (G.onChow (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
          ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s) k
          (chowGroupRestrict C (g ≫ sY)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
            (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) (k + 1) α)) =
      chowGroupRestrict C (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) _
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι
        (testPiece_comp_structureMorphism C sY UY a
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i) k
        (G.onChow (g ≫ sY) L s k α) := by
    rw [← hR, chowGroupRestrict_comp, chowGroupRestrict_congr C _ _ _ _ k
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι
      (zeroSchemeTestPieceIso_hom_comp UY a g L s i) hTPr]
    rfl
  have hGi : G.onChow (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
        ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s) k
        (chowGroupRestrict C (g ≫ sY)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
          (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i) (k + 1) α) =
      properChowPushforward C
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY))
        (((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UY (a i)).ι ≫ sY))
        (zeroSchemeTestPieceIso UY a g L s i).hom hκYL k hfacκ
        (chowGroupRestrict C (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) _
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι
          (testPiece_comp_structureMorphism C sY UY a
            ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i) k
          (G.onChow (g ≫ sY) L s k α)) :=
    (eq_chowPushforwardOfIso_chowGroupRestrict C
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY)))
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY))
        (zeroSchemeTestPieceIso UY a g L s i).hom hκY k
        (G.onChow (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
          ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s) k
          (chowGroupRestrict C (g ≫ sY)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY))
            (g ⁻¹ᵁ UY (a i)).ι (testPiece_comp_structureMorphism C sY UY a g i)
            (k + 1) α))).trans
      (DFunLike.congr_arg (chowPushforwardOfIso C
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY))
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ ((UY (a i)).ι ≫ sY)))
        (zeroSchemeTestPieceIso UY a g L s i).hom hκY k) hδ)
  -- the comparison of the two presentations of the `i`-th piece, on cap products
  have hwκ : pullback.snd (pieceMap f UX UY a ha i)
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫
      (zeroSchemeTestPieceIso UY a g L s i).hom =
        zeroSchemeTestPieceBaseChange f UX UY a ha g L s i ≫
          pullback.snd (pieceMap f UX UY a ha i)
            ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
              g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) :=
    (zeroSchemeTestPieceBaseChange_snd f UX UY a ha g L s i).symm
  have hsqκ := IsPullback.of_vert_isIso (CommSq.mk hwκ)
  have hubc : zeroSchemeTestPieceBaseChange f UX UY a ha g L s i ≫
      (pullback.fst (pieceMap f UX UY a ha i)
          ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
            g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) =
      pullback.fst (pieceMap f UX UY a ha i)
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫
        ((UX i).ι ≫ sX) := by
    rw [← Category.assoc, zeroSchemeTestPieceBaseChange_fst]
  have hfacκ' := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
    (zeroSchemeTestPieceBaseChange f UX UY a ha g L s i) hubc (k - p)
  have hpn := BivariantClass.proper_naturality_of_eq C G ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
    (pieceMap f UX UY a ha i)
    (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p (c i)
    ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
      g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
    (zeroSchemeTestPieceIso UY a g L s i).hom
    (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl)
    (zeroSchemeTestPieceIso_hom_comp_resLE UY a g L s i)
    (zeroSchemeTestPieceBaseChange f UX UY a ha g L s i) hsqκ
    (zeroSchemeTestPieceBaseChange_fst f UX UY a ha g L s i) k hκYL hfacκ hfacκ'
    (chowGroupRestrict C (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) _
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι
      (testPiece_comp_structureMorphism C sY UY a
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i) k
      (G.onChow (g ≫ sY) L s k α))
  have heqv : eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (zeroScheme_pieceTestProjection f UX UY a ha g L s i)) ≫
      ((zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))) =
      (Stacks.Divisors.zeroScheme
          (pullback (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
          ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))).obj
            ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L))
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (pieceMap f UX UY a ha i)
              (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
            ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s))).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) := by
    rw [← Category.assoc,
      subschemeι_eqToHom (zeroScheme_pieceTestProjection f UX UY a ha g L s i)]
  have heqvinv : eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (zeroScheme_pieceTestProjection f UX UY a ha g L s i).symm) ≫
      ((Stacks.Divisors.zeroScheme
          (pullback (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
          ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))).obj
            ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L))
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (pieceMap f UX UY a ha i)
              (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
            ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s))).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))) =
      (zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) := by
    rw [← Category.assoc,
      subschemeι_eqToHom (zeroScheme_pieceTestProjection f UX UY a ha g L s i).symm]
  -- the characterizing property of the assembled cap operation at the two test schemes
  have hBR := bivariantPieceAssemblyCap_restrict C G sX sY f hf UX UY a ha hX p c
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k (G.onChow (g ≫ sY) L s k α) i
  have hBR2 := bivariantPieceAssemblyCap_restrict C G sX sY f hf UX UY a ha hX p c g (k + 1) α i
  -- the three identifications of the `i`-th piece compose to the comparison
  have hfinal := chowGroupRestrict_properChowPushforward_comp_of_isIso C _ _ _ _
    (zeroSchemeTestPieceBaseChange f UX UY a ha g L s i)
    (zeroSchemeBaseChangeIso (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
      ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)).hom
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (zeroScheme_pieceTestProjection f UX UY a ha g L s i).symm))
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (zeroScheme_pieceTestProjection f UX UY a ha g L s i)))
    (zeroSchemePieceComparison f UX UY a ha g L s i).hom hubc hbasei heqvinv heqv hq'
    (by simp) rfl (k - p) hfacκ' hfaci hfac'
    ((c i).cap (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) k
      (chowGroupRestrict C (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY)
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl ≫
          ((UY (a i)).ι ≫ sY))
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι
        (testPiece_comp_structureMorphism C sY UY a
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i) k
        (G.onChow (g ≫ sY) L s k α)))
  -- putting the two sides together
  refine (hL.trans (DFunLike.congr_arg (properChowPushforward C _ _
    (zeroSchemePieceComparison f UX UY a ha g L s i).hom hq' (k - p) hfac') hBR)).trans
    (Eq.symm (hRgysO.trans ?_))
  refine (DFunLike.congr_arg (G.onChow (pullback.fst (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
      ((Scheme.Modules.pullback (pieceTestProjection f UX UY a ha g i)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pieceTestProjection f UX UY a ha g i) L s)
      (k - p))
    (hcast.trans (congrArg (Eq.mp (congrArg (chowGroup C
      (pullback.fst (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))) hidx)) hBR2))).trans ?_
  exact hC.symm.trans ((DFunLike.congr_arg (chowGroupRestrict C _ _
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme
        (zeroScheme_pieceTestProjection f UX UY a ha g L s i).symm)) heqvinv (k - p))
    (hci.symm.trans (DFunLike.congr_arg (properChowPushforward C _ _
        (zeroSchemeBaseChangeIso (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
          ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)).hom hbasei
        (k - p) hfaci)
      ((DFunLike.congr_arg ((c i).cap ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
        g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) k) hGi).trans hpn)))).trans hfinal)

end Assembly

end Stacks.Chow

end
