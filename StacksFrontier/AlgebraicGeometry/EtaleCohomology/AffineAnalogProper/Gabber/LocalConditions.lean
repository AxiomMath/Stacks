module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleReduction

/-!
# Vanishing and constancy of an étale sheaf along a subset

For an abelian sheaf `G` on the small étale site of a scheme `X` and a subset `S ⊆ X` this file
introduces two conditions, read through inverse images along immersions:

* `Stacks.EtaleCohomology.VanishesOffSet G S`: the inverse image of `G` along every immersion
  whose image misses `S` is zero;
* `Stacks.EtaleCohomology.IsConstantOnSet G S E`: the inverse image of `G` along every immersion
  of a reduced scheme with image inside `S` is the constant sheaf with value `E`.

and shows how they pass through the two halves `j_! j^{-1} G` and `i_* i^{-1} G` of the sequence
`0 → j_! j^{-1} G → G → i_* i^{-1} G → 0` of an open immersion `j` and a closed immersion `i`.
These are the bookkeeping steps of the dévissage of a constructible sheaf into extensions by zero
of constant sheaves on locally closed pieces.

## Main definitions

* `Stacks.EtaleCohomology.VanishesOffSet`, `Stacks.EtaleCohomology.IsConstantOnSet`.

## Main results

* `Stacks.EtaleCohomology.VanishesOffSet.extensionByZero`,
  `Stacks.EtaleCohomology.IsConstantOnSet.extensionByZero`: the open half.
* `Stacks.EtaleCohomology.VanishesOffSet.directImage`,
  `Stacks.EtaleCohomology.IsConstantOnSet.directImage`: the closed half.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The abelian sheaf `G` on `X_étale` vanishes off `S ⊆ X`: its inverse image along every
immersion whose image is disjoint from `S` is zero. -/
def VanishesOffSet {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (S : Set X) : Prop :=
  ∀ ⦃W : Scheme.{u}⦄ (ι : W ⟶ X) [IsImmersion ι], Disjoint (Set.range ι.base) S →
    IsZero ((etaleAbelianInverseImage.{u, 0} ι).obj G)

/-- The abelian sheaf `G` on `X_étale` is constant with value `E` on `S ⊆ X`: its inverse image
along every immersion of a reduced scheme with image inside `S` is the constant sheaf `E`. -/
def IsConstantOnSet {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (S : Set X) (E : AddCommGrpCat.{u + 1}) : Prop :=
  ∀ ⦃W : Scheme.{u}⦄ (ι : W ⟶ X) [IsImmersion ι] [IsReduced W], Set.range ι.base ⊆ S →
    Nonempty ((etaleAbelianInverseImage.{u, 0} ι).obj G ≅
      (constantSheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)

/-- If `G` vanishes off `S` and `S ⊆ S'`, then `G` vanishes off `S'`. -/
theorem VanishesOffSet.mono {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {S S' : Set X} (h : VanishesOffSet G S) (hS : S ⊆ S') : VanishesOffSet G S' :=
  fun _ ι _ hd => h ι (hd.mono_right hS)

/-- If `G` is constant with value `E` on `S` and `S' ⊆ S`, then `G` is constant with value `E` on
`S'`. -/
theorem IsConstantOnSet.mono {X : Scheme.{u}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {S S' : Set X}
    {E : AddCommGrpCat.{u + 1}} (h : IsConstantOnSet G S E) (hS : S' ⊆ S) :
    IsConstantOnSet G S' E :=
  fun _ ι _ _ hs => h ι (hs.trans hS)

/-- Vanishing off `S` is invariant under isomorphism of sheaves. -/
theorem VanishesOffSet.of_iso {X : Scheme.{u}}
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {S : Set X}
    (h : VanishesOffSet G S) (e : G ≅ G') : VanishesOffSet G' S :=
  fun _ ι _ hd => (h ι hd).of_iso ((etaleAbelianInverseImage.{u, 0} ι).mapIso e).symm

/-- Constancy with value `E` on `S` is invariant under isomorphism of sheaves. -/
theorem IsConstantOnSet.of_iso {X : Scheme.{u}}
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {S : Set X}
    {E : AddCommGrpCat.{u + 1}} (h : IsConstantOnSet G S E) (e : G ≅ G') :
    IsConstantOnSet G' S E :=
  fun _ ι _ _ hs => (h ι hs).map fun e' => ((etaleAbelianInverseImage.{u, 0} ι).mapIso e).symm ≪≫ e'

/-- If `f ≫ k = g ≫ ι` and the range of `ι` misses `S ∩ range k`, then the range of `f ≫ k`
misses `S`. -/
theorem disjoint_range_comp_of_comp_eq {X U W P : Scheme.{u}} {k : U ⟶ X} {ι : W ⟶ X}
    {f : P ⟶ U} {g : P ⟶ W} (hw : f ≫ k = g ≫ ι) {S : Set X}
    (hd : Disjoint (Set.range ι.base) (S ∩ Set.range k.base)) :
    Disjoint (Set.range (f ≫ k).base) S := by
  rw [Set.disjoint_left]
  rintro x ⟨y, rfl⟩ hx
  have hι : (f ≫ k).base y ∈ Set.range ι.base := by
    rw [hw]
    exact ⟨_, rfl⟩
  exact Set.disjoint_left.mp hd hι ⟨hx, _, rfl⟩

/-- If `G` vanishes off `S` and `f ≫ k` misses `S`, then `f⁻¹ k⁻¹ G` is zero. -/
private theorem isZero_inverseImage_inverseImage {X U P : Scheme.{u}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {S : Set X} (h : VanishesOffSet G S)
    (k : U ⟶ X) (f : P ⟶ U) [IsImmersion (f ≫ k)] (hd : Disjoint (Set.range (f ≫ k).base) S) :
    IsZero ((etaleAbelianInverseImage.{u, 0} f).obj ((etaleAbelianInverseImage.{u, 0} k).obj G)) :=
  IsZero.of_iso (h (f ≫ k) hd)
    ((etaleAbelianInverseImageCompIso'.{u, 0} f k (f ≫ k) rfl).app G).symm

/-- If `ι = ι' ≫ k` and `k⁻¹ G' ≅ k⁻¹ G`, then `ι⁻¹ G` constant gives `ι⁻¹ G'` constant. -/
private theorem nonempty_iso_constantSheaf_of_comp_eq {X U W : Scheme.{u}} {k : U ⟶ X}
    {ι' : W ⟶ U} {ι : W ⟶ X} (hfac : ι = ι' ≫ k)
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {E : AddCommGrpCat.{u + 1}}
    (φ : (etaleAbelianInverseImage.{u, 0} k).obj G' ≅ (etaleAbelianInverseImage.{u, 0} k).obj G)
    (e : (etaleAbelianInverseImage.{u, 0} ι).obj G ≅
      (constantSheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) :
    Nonempty ((etaleAbelianInverseImage.{u, 0} ι).obj G' ≅
      (constantSheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) :=
  ⟨((etaleAbelianInverseImageCompIso'.{u, 0} ι' k ι hfac).app G') ≪≫
    (etaleAbelianInverseImage.{u, 0} ι').mapIso φ ≪≫
    ((etaleAbelianInverseImageCompIso'.{u, 0} ι' k ι hfac).app G).symm ≪≫ e⟩

section Open

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **Vanishing passes to the extension by zero of the restriction to an open.** -/
theorem VanishesOffSet.extensionByZero {S : Set X} (h : VanishesOffSet G S) :
    VanishesOffSet ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj G))
      (S ∩ Set.range j.base) := by
  intro W ι _ hd
  let fst := pullback.fst j ι
  let snd := pullback.snd j ι
  have hz : IsZero ((etaleAbelianInverseImage.{u, 0} fst).obj
      ((etaleRestriction.{u, 0} j).obj G)) :=
    IsZero.of_iso (isZero_inverseImage_inverseImage h j fst
      (disjoint_range_comp_of_comp_eq pullback.condition hd))
      ((etaleAbelianInverseImage.{u, 0} fst).mapIso
        ((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app G).symm)
  have : (EtaleCohomology.extensionByZero.{u, 0} snd).IsLeftAdjoint :=
    (extensionByZeroAdj.{u, 0} snd).isLeftAdjoint
  exact IsZero.of_iso (Functor.map_isZero (EtaleCohomology.extensionByZero.{u, 0} snd) hz)
    ((extensionByZeroBaseChangeIso.{u, 0} j ι).app ((etaleRestriction.{u, 0} j).obj G)).symm

/-- **Constancy passes to the extension by zero of the restriction to an open.** -/
theorem IsConstantOnSet.extensionByZero {S : Set X} {E : AddCommGrpCat.{u + 1}}
    (h : IsConstantOnSet G S E) :
    IsConstantOnSet ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj G))
      (S ∩ Set.range j.base) E := by
  intro W ι _ _ hs
  obtain ⟨e⟩ := h ι (fun x hx => (hs hx).1)
  exact nonempty_iso_constantSheaf_of_comp_eq
    (IsOpenImmersion.lift_fac j ι fun x hx => (hs hx).2).symm
    (((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app _) ≪≫
      (asIso ((extensionByZeroAdj.{u, 0} j).unit.app ((etaleRestriction.{u, 0} j).obj G))).symm ≪≫
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app G).symm) e

end Open

section Closed

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **Vanishing passes to the direct image of the restriction to a closed subscheme.** -/
theorem VanishesOffSet.directImage {S : Set X} (h : VanishesOffSet G S) :
    VanishesOffSet
      ((etaleAbelianDirectImage.{u, 0} i).obj ((etaleAbelianInverseImage.{u, 0} i).obj G))
      (S ∩ Set.range i.base) := by
  intro W ι _ hd
  let fst := pullback.fst ι i
  let snd := pullback.snd ι i
  have sq : IsPullback fst snd ι i := IsPullback.of_hasPullback ι i
  have hBC : IsIso (smallEtaleBaseChangeAb ι i fst snd sq.w) :=
    isIso_smallEtaleBaseChangeAb_of_isIntegralHom ι i fst snd sq
  let K := (etaleAbelianInverseImage.{u, 0} i).obj G
  let e : (etaleAbelianInverseImage.{u, 0} ι).obj ((etaleAbelianDirectImage.{u, 0} i).obj K) ≅
      (etaleAbelianDirectImage.{u, 0} fst).obj ((etaleAbelianInverseImage.{u, 0} snd).obj K) :=
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange ι)
        AddCommGrpCat.{u + 1} X.smallEtaleTopology W.smallEtaleTopology).app _).symm ≪≫
      (asIso (smallEtaleBaseChangeAb ι i fst snd sq.w)).app K ≪≫
      (etaleAbelianDirectImage.{u, 0} fst).mapIso
        ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange snd)
          AddCommGrpCat.{u + 1} Z.smallEtaleTopology (pullback ι i).smallEtaleTopology).app K)
  have hz : IsZero ((etaleAbelianInverseImage.{u, 0} snd).obj K) :=
    isZero_inverseImage_inverseImage h i snd
      (disjoint_range_comp_of_comp_eq pullback.condition.symm hd)
  have : (etaleAbelianDirectImage.{u, 0} fst).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} fst).isRightAdjoint
  exact IsZero.of_iso (Functor.map_isZero _ hz) e

/-- **Constancy passes to the direct image of the restriction to a closed subscheme.** -/
theorem IsConstantOnSet.directImage {S : Set X} {E : AddCommGrpCat.{u + 1}}
    (h : IsConstantOnSet G S E) :
    IsConstantOnSet
      ((etaleAbelianDirectImage.{u, 0} i).obj ((etaleAbelianInverseImage.{u, 0} i).obj G))
      (S ∩ Set.range i.base) E := by
  intro W ι _ _ hs
  obtain ⟨ι', hfac⟩ := Scheme.exists_comp_eq_of_isImmersion_of_isReduced i ι
    (fun x hx => (hs hx).2)
  obtain ⟨e⟩ := h ι (fun x hx => (hs hx).1)
  have hu := isIso_etaleAbelianInverseImage_map_unit.{u, 0} i G
  exact nonempty_iso_constantSheaf_of_comp_eq hfac.symm
    (asIso ((etaleAbelianInverseImage.{u, 0} i).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app G))).symm e

end Closed

end Stacks.EtaleCohomology
