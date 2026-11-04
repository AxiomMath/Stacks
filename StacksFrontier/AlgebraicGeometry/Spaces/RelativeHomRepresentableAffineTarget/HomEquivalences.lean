module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Hom equivalences for the relative morphism functor of a coproduct-of-affines target

Transport of the relative morphism functor along a fully faithful functor preserving the relevant
limits, and the identification of morphisms out of a product in a slice `Over Q` with morphisms
out of a pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w u'

namespace AlgebraicGeometry.RelativeHomAffineTarget

noncomputable def pullbackHomEquiv
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {D : Type w} [Category.{u'} D] [HasPullbacks D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [PreservesLimitsOfShape WalkingCospan F]
    {T Z X Q : C} (a : T ⟶ Q) (z : Z ⟶ Q) (x : X ⟶ Q) :
    {b : pullback a z ⟶ X // b ≫ x = pullback.snd a z ≫ z} ≃
      {b : pullback (F.map a) (F.map z) ⟶ F.obj X //
        b ≫ F.map x = pullback.snd (F.map a) (F.map z) ≫ F.map z} where
  toFun b := ⟨inv (pullbackComparison F a z) ≫ F.map b.val, by
    rw [Category.assoc, ← F.map_comp, b.property, F.map_comp]
    rw [← pullbackComparison_comp_snd F a z]
    simp⟩
  invFun b := ⟨F.preimage (pullbackComparison F a z ≫ b.val), by
    apply F.map_injective
    rw [F.map_comp, F.map_preimage, Category.assoc, b.property,
      ← Category.assoc, pullbackComparison_comp_snd, ← F.map_comp]⟩
  left_inv b := by
    apply Subtype.ext
    apply F.map_injective
    simp
  right_inv b := by
    apply Subtype.ext
    simp

lemma pullbackHomEquiv_natural
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {D : Type w} [Category.{u'} D] [HasPullbacks D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [PreservesLimitsOfShape WalkingCospan F]
    {T T' Z X Q : C} (a : T ⟶ Q) (z : Z ⟶ Q) (x : X ⟶ Q)
    (t : T' ⟶ T) (b : pullback a z ⟶ X)
    (hb : b ≫ x = pullback.snd a z ≫ z) :
    (pullbackHomEquiv F (t ≫ a) z x
      ⟨pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫ b,
        by simp [Category.assoc, hb]⟩).val =
      pullback.map (F.map (t ≫ a)) (F.map z) (F.map a) (F.map z)
        (F.map t) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
        (pullbackHomEquiv F a z x ⟨b, hb⟩).val := by
  change inv (pullbackComparison F (t ≫ a) z) ≫
      F.map (pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) _ _ ≫ b) =
    pullback.map (F.map (t ≫ a)) (F.map z) (F.map a) (F.map z)
      (F.map t) (𝟙 _) (𝟙 _) _ _ ≫
      inv (pullbackComparison F a z) ≫ F.map b
  rw [F.map_comp _ b, ← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_epi (pullbackComparison F (t ≫ a) z)).mp
  simp only [IsIso.hom_inv_id_assoc]
  apply (cancel_mono (pullbackComparison F a z)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackComparison_comp_fst,
      pullbackComparison_comp_fst_assoc, pullback.map, pullback.lift_fst, ← F.map_comp]
  · simp only [Category.assoc, pullbackComparison_comp_snd,
      pullback.map, pullback.lift_snd, Category.comp_id, ← F.map_comp]

noncomputable def representableBy_restrict
    {C : Type v} [Category.{u} C] {D : Type w} [Category.{u} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {H : Dᵒᵖ ⥤ Type u} {W : C}
    (r : H.RepresentableBy (F.obj W)) :
    (F.op ⋙ H).RepresentableBy W where
  homEquiv := (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans r.homEquiv
  homEquiv_comp f g := by
    change r.homEquiv (F.map (f ≫ g)) = H.map (F.map f).op (r.homEquiv (F.map g))
    rw [F.map_comp, r.homEquiv_comp]

noncomputable def relativeHomComparison
    {C : Type v} [Category.{u} C] [HasBinaryProducts C]
    {D : Type w} [Category.{u} D] [HasBinaryProducts D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    (Z X : C) :
    (prod.functor.obj Z).op ⋙ yoneda.obj X ≅
      F.op ⋙ (prod.functor.obj (F.obj Z)).op ⋙ yoneda.obj (F.obj X) := by
  let e : yoneda.obj X ≅ F.op ⋙ yoneda.obj (F.obj X) :=
    NatIso.ofComponents (fun T =>
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv).toIso)
      (by intro T T' f; ext g; exact F.map_comp f.unop g)
  exact Functor.isoWhiskerLeft (prod.functor.obj Z).op e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (prodComparisonNatIso F Z).symm)
      (yoneda.obj (F.obj X)) ≪≫
    Functor.associator F.op (prod.functor.obj (F.obj Z)).op (yoneda.obj (F.obj X))

noncomputable def relativeHomRepresentableBy_of_fullyFaithful
    {C : Type v} [Category.{u} C] [HasBinaryProducts C]
    {D : Type w} [Category.{u} D] [HasBinaryProducts D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    (Z X W : C)
    (r : ((prod.functor.obj (F.obj Z)).op ⋙ yoneda.obj (F.obj X)).RepresentableBy
      (F.obj W)) :
    ((prod.functor.obj Z).op ⋙ yoneda.obj X).RepresentableBy W :=
  (representableBy_restrict F r).ofIso (relativeHomComparison F Z X).symm


noncomputable def overProductHomEquiv
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {T Z X Q : C} [HasBinaryProducts (Over Q)] (a : T ⟶ Q) (z : Z ⟶ Q) (x : X ⟶ Q) :
    (Over.mk z ⨯ Over.mk a ⟶ Over.mk x) ≃
      {b : pullback a z ⟶ X // b ≫ x = pullback.snd a z ≫ z} := by
  let P := Over.mk z ⨯ Over.mk a
  let e : P.left ≅ pullback a z :=
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : P ⟶ Over.mk z) (prod.snd : P ⟶ Over.mk a))
      (prodIsProd (Over.mk z) (Over.mk a))).flip.isoPullback
  have he : e.hom ≫ pullback.snd a z = (prod.fst : P ⟶ Over.mk z).left := by
    simp [e]
  have hei : e.inv ≫ (prod.fst : P ⟶ Over.mk z).left = pullback.snd a z := by
    rw [← he]
    simp
  refine
    { toFun := fun b => ⟨e.inv ≫ b.left, ?_⟩
      invFun := fun b => Over.homMk (e.hom ≫ b.val) ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hb : b.left ≫ x = P.hom := Over.w b
    have hf : (prod.fst : P ⟶ Over.mk z).left ≫ z = P.hom :=
      Over.w (prod.fst : P ⟶ Over.mk z)
    rw [Category.assoc, hb, ← hf, ← Category.assoc, hei]
  · change (e.hom ≫ b.val) ≫ x = P.hom
    rw [Category.assoc, b.property, ← Category.assoc, he]
    exact Over.w (prod.fst : P ⟶ Over.mk z)
  · intro b
    ext
    simp
  · intro b
    apply Subtype.ext
    simp

noncomputable def sigmaOverHomEquiv
    {C : Type v} [Category.{u} C] {Q T : C} (W : Over Q) :
    (Σ a : T ⟶ Q, Over.mk a ⟶ W) ≃ (T ⟶ W.left) := by
  let π : (Σ a : T ⟶ Q, Over.mk a ⟶ W) → (T ⟶ W.left) := fun p => p.2.left
  have hπ : Function.Injective π := by
    rintro ⟨a, f⟩ ⟨b, g⟩ h
    have hab : a = b := (Over.w f).symm.trans ((congrArg (fun k => k ≫ W.hom) h).trans
      (Over.w g))
    cases hab
    congr 1
    exact Over.OverMorphism.ext h
  exact
    { toFun := π
      invFun := fun f => ⟨f ≫ W.hom, Over.homMk f rfl⟩
      left_inv := fun p => hπ rfl
      right_inv := fun _ => rfl }


lemma overProductHomEquiv_natural
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {T T' Z X Q : C} [HasBinaryProducts (Over Q)]
    (a : T ⟶ Q) (z : Z ⟶ Q) (x : X ⟶ Q) (t : T' ⟶ T)
    (b : Over.mk z ⨯ Over.mk a ⟶ Over.mk x) :
    (overProductHomEquiv (t ≫ a) z x
      (prod.map (𝟙 _)
        (Over.homMk t rfl : Over.mk (t ≫ a) ⟶ Over.mk a) ≫ b)).val =
      pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫
        (overProductHomEquiv a z x b).val := by
  let e {S : C} (a : S ⟶ Q) : (Over.mk z ⨯ Over.mk a).left ≅ pullback a z :=
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : Over.mk z ⨯ Over.mk a ⟶ Over.mk z) prod.snd)
      (prodIsProd (Over.mk z) (Over.mk a))).flip.isoPullback
  have he₁ {S : C} (a : S ⟶ Q) : (e a).hom ≫ pullback.fst a z =
      (prod.snd : Over.mk z ⨯ Over.mk a ⟶ Over.mk a).left :=
    IsPullback.isoPullback_hom_fst _
  have he₂ {S : C} (a : S ⟶ Q) : (e a).hom ≫ pullback.snd a z =
      (prod.fst : Over.mk z ⨯ Over.mk a ⟶ Over.mk z).left :=
    IsPullback.isoPullback_hom_snd _
  change (e (t ≫ a)).inv ≫ (prod.map (𝟙 (Over.mk z))
      (Over.homMk t rfl : Over.mk (t ≫ a) ⟶ Over.mk a) ≫ b).left =
    pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) _ _ ≫ (e a).inv ≫ b.left
  simp only [Over.comp_left, ← Category.assoc]
  congr 1
  apply (cancel_epi (e (t ≫ a)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_mono (e a).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, he₁ a, pullback.map, pullback.lift_fst]
    rw [← Over.comp_left, prod.map_snd]
    simp only [Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, he₁ (t ≫ a)]
  · simp only [Category.assoc, he₂ a, pullback.map, pullback.lift_snd, Category.comp_id]
    rw [← Over.comp_left, prod.map_fst]
    simpa only [Category.comp_id] using (he₂ (t ≫ a)).symm

end AlgebraicGeometry.RelativeHomAffineTarget

end
