module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforward
import all StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforward
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# Pushforward of pro-objects along a functor

A functor `F : 𝒟 ⥤ 𝒟'` acts on pro-objects termwise: it sends the pro-object of an inverse
sequence `(M_n)` to that of `(F M_n)`. On functors of points this is the left Kan extension along
`F`, which carries the corepresentable functor `Mor(M, -)` to `Mor(F M, -)` and commutes with
colimits, so that

`Lan_F (colim_n Mor(M_n, -)) = colim_n Mor(F M_n, -)`.

This is `CategoryTheory.ProSeq.map`. No adjoint of `F` is needed. For the duality chapter
`𝒟 = D^b_{Coh}(𝒪_{X'})`, `𝒟' = D^b_{Coh}(𝒪_X)` and `F = Rf_*` for a proper morphism `f`; the
functor built here is the one written `Rf_*` again when it is applied to the pro-objects `Rj_! K`
of [Stacks, Tag 0G4N], as in the definition `Rf_! = Rf̄_* ∘ Rj_!` of [Stacks, Section 0G4Z]. A
right adjoint of `Rf_*` inside `D^b_{Coh}` need not exist (for a closed immersion
`Spec k ⟶ Spec k[ε]` it would have to be cohomologically unbounded), which is why the pushforward
is not defined through one.

## Main definitions

* `CategoryTheory.ProSeq.map`: the functor `Pro-𝒟 ⥤ Pro-𝒟'` induced by an arbitrary functor `F`.

## Main results

* `CategoryTheory.Pro.lanSeqHomColimIso`: `Lan_F (colim_n Mor(M_n, -)) = colim_n Mor(F M_n, -)`.
* `CategoryTheory.ProSeq.mapOfIso`: `ProSeq.map F` sends the pro-object of `(M_n)` to that of
  `(F M_n)`.
* `CategoryTheory.ProSeq.liftIso`: an isomorphism of families of functors of points is an
  isomorphism of the families of pro-objects they define.
* `CategoryTheory.ProSeq.mapComp`, `CategoryTheory.ProSeq.mapIsoOfIso`: `ProSeq.map` is
  compatible with composition and with isomorphisms of functors.

## References

* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u' w₁ w₂

namespace CategoryTheory

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒟' : Type u'} [Category.{v} 𝒟']

namespace ProSeq

end ProSeq

/-! ### Pushforward along an arbitrary functor -/

section Map

variable (F : 𝒟 ⥤ 𝒟')

namespace Pro

/-- The leg of `colim_n Mor(M_n, -)` at `n` is the transformation out of `Mor(M_n, -)` that the
co-Yoneda lemma attaches to the class of the identity of `M_n`. -/
public lemma ι_eq_coyonedaEquiv_symm (M : ℕᵒᵖ ⥤ 𝒟) (n : ℕ) :
    colimit.ι (M.op ⋙ coyoneda) (op (op n)) =
      coyonedaEquiv.symm (seqStage M (𝟙 (M.obj (op n)))) := by
  rw [Equiv.eq_symm_apply]
  rfl

/-- The class of a transition morphism `M_m ⟶ M_n` at stage `m` is the class of the identity of
`M_n` at stage `n`. -/
public lemma seqStage_tr (M : ℕᵒᵖ ⥤ 𝒟) {n m : ℕ} (h : n ≤ m) :
    seqStage M (n := m) (InverseSequence.tr M h) = seqStage M (𝟙 (M.obj (op n))) := by
  simpa using seqStage_transition M h (𝟙 _)

/-- A transformation out of a corepresentable functor, composed with a transformation, corresponds
under the co-Yoneda lemma to the image of the element. -/
public lemma coyonedaEquiv_symm_comp {X : 𝒟} {A B : 𝒟 ⥤ Type v} (x : A.obj X) (η : A ⟶ B) :
    coyonedaEquiv.symm x ≫ η = coyonedaEquiv.symm (η.app X x) := by
  rw [Equiv.eq_symm_apply, coyonedaEquiv_apply]
  change η.app X (A.map (𝟙 X) x) = _
  rw [A.map_id]
  rfl

/-- The functor of points sends `g` to postcomposition with `g`, applied to the class of the
identity. -/
private theorem seqHomColim_map_seqStage_id (M : ℕᵒᵖ ⥤ 𝒟) {L : 𝒟} {n : ℕ}
    (g : M.obj (op n) ⟶ L) :
    (seqHomColim M).map g (seqStage M (𝟙 (M.obj (op n)))) = seqStage M g := by
  rw [seqHomColim_map_seqStage, Category.id_comp]

/-- The transformation `colim_n Mor(M_n, -) ⟶ colim_n Mor(F M_n, F -)` applying `F` to the
representatives: the class of `g : M_n ⟶ L` goes to the class of `F g`. -/
public def seqHomColimToComp (M : ℕᵒᵖ ⥤ 𝒟) : seqHomColim M ⟶ F ⋙ seqHomColim (M ⋙ F) :=
  colimit.desc (M.op ⋙ coyoneda)
    { pt := F ⋙ seqHomColim (M ⋙ F)
      ι :=
        { app := fun n => coyonedaEquiv.symm
            (seqStage (M ⋙ F) (n := n.unop.unop) (𝟙 (F.obj (M.obj n.unop))))
          naturality := by
            rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ a
            have h : n ≤ m := leOfHom a.unop.unop
            obtain rfl : a = (homOfLE h).op.op := Subsingleton.elim _ _
            change coyoneda.map (InverseSequence.tr M h).op ≫ _ = _ ≫ 𝟙 _
            rw [Category.comp_id, ← coyonedaEquiv_symm_map]
            congr 1
            change (seqHomColim (M ⋙ F)).map (F.map (InverseSequence.tr M h)) _ = _
            rw [seqHomColim_map_seqStage]
            exact (congrArg (seqStage (M ⋙ F)) (Category.id_comp _)).trans
              (seqStage_tr (M ⋙ F) h) } }

/-- `Pro.seqHomColimToComp` sends the class of `g : M_n ⟶ L` to the class of `F g`. -/
public lemma seqHomColimToComp_app_seqStage (M : ℕᵒᵖ ⥤ 𝒟) {L : 𝒟} {n : ℕ}
    (g : M.obj (op n) ⟶ L) :
    (seqHomColimToComp F M).app L (seqStage M g) = seqStage (M ⋙ F) (n := n) (F.map g) := by
  have h₂ : (seqHomColimToComp F M).app (M.obj (op n)) (seqStage M (𝟙 _)) =
      seqStage (M ⋙ F) (n := n) (𝟙 (F.obj (M.obj (op n)))) := by
    change (colimit.ι (M.op ⋙ coyoneda) (op (op n)) ≫ seqHomColimToComp F M).app _ (𝟙 _) = _
    rw [seqHomColimToComp, colimit.ι_desc]
    exact coyonedaEquiv.apply_symm_apply _
  rw [← seqHomColim_map_seqStage_id M g, NatTrans.naturality_apply, h₂]
  exact seqHomColim_map_seqStage_id (M ⋙ F) (F.map g)

variable [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A]

/-- The comparison `Lan_F (colim_n Mor(M_n, -)) ⟶ colim_n Mor(F M_n, -)`, adjoint to
`Pro.seqHomColimToComp`. -/
public def lanSeqHomColimHom (M : ℕᵒᵖ ⥤ 𝒟) :
    F.lan.obj (seqHomColim M) ⟶ seqHomColim (M ⋙ F) :=
  ((F.lanAdjunction (Type v)).homEquiv _ _).symm (seqHomColimToComp F M)

/-- The unit of the left Kan extension followed by `Pro.lanSeqHomColimHom` is
`Pro.seqHomColimToComp`. -/
public lemma lanUnit_comp_lanSeqHomColimHom (M : ℕᵒᵖ ⥤ 𝒟) :
    F.lanUnit.app (seqHomColim M) ≫ Functor.whiskerLeft F (lanSeqHomColimHom F M) =
      seqHomColimToComp F M := by
  have h := ((F.lanAdjunction (Type v)).homEquiv _ _).apply_symm_apply (seqHomColimToComp F M)
  rw [Adjunction.homEquiv_unit, Functor.lanAdjunction_unit] at h
  exact h

/-- The comparison `colim_n Mor(F M_n, -) ⟶ Lan_F (colim_n Mor(M_n, -))`: the class of
`h : F M_n ⟶ L` goes to the image under `h` of the unit at the class of the identity of `M_n`. -/
public def lanSeqHomColimInv (M : ℕᵒᵖ ⥤ 𝒟) :
    seqHomColim (M ⋙ F) ⟶ F.lan.obj (seqHomColim M) :=
  colimit.desc ((M ⋙ F).op ⋙ coyoneda)
    { pt := F.lan.obj (seqHomColim M)
      ι :=
        { app := fun n => coyonedaEquiv.symm ((F.lanUnit.app (seqHomColim M)).app (M.obj n.unop)
            (seqStage M (n := n.unop.unop) (𝟙 (M.obj n.unop))))
          naturality := by
            rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ a
            have h : n ≤ m := leOfHom a.unop.unop
            obtain rfl : a = (homOfLE h).op.op := Subsingleton.elim _ _
            change coyoneda.map (F.map (InverseSequence.tr M h)).op ≫ _ = _ ≫ 𝟙 _
            rw [Category.comp_id, ← coyonedaEquiv_symm_map]
            congr 1
            have hn := NatTrans.naturality_apply (F.lanUnit.app (seqHomColim M))
              (InverseSequence.tr M h) (seqStage M (n := m) (𝟙 _))
            change _ = (F.lan.obj (seqHomColim M)).map (F.map (InverseSequence.tr M h)) _ at hn
            change (F.lan.obj (seqHomColim M)).map (F.map (InverseSequence.tr M h)) _ = _
            rw [← hn]
            congr 1
            exact (seqHomColim_map_seqStage M _ _).trans
              ((congrArg (seqStage M) (Category.id_comp _)).trans (seqStage_tr M h)) } }

/-- `Pro.lanSeqHomColimInv` sends the class of the identity of `F M_n` to the unit at the class of
the identity of `M_n`. -/
public lemma lanSeqHomColimInv_app_seqStage_id (M : ℕᵒᵖ ⥤ 𝒟) (n : ℕ) :
    (lanSeqHomColimInv F M).app ((M ⋙ F).obj (op n))
        (seqStage (M ⋙ F) (n := n) (𝟙 ((M ⋙ F).obj (op n)))) =
      (F.lanUnit.app (seqHomColim M)).app (M.obj (op n)) (seqStage M (𝟙 (M.obj (op n)))) := by
  change (colimit.ι ((M ⋙ F).op ⋙ coyoneda) (op (op n)) ≫ lanSeqHomColimInv F M).app _
    (𝟙 _) = _
  rw [lanSeqHomColimInv, colimit.ι_desc]
  exact coyonedaEquiv.apply_symm_apply _

/-- **The left Kan extension of a functor of points of an inverse sequence.**
`Lan_F (colim_n Mor(M_n, -)) = colim_n Mor(F M_n, -)`: the pro-object of `(M_n)` is carried by `F`
to the pro-object of `(F M_n)`. -/
public def lanSeqHomColimIso (M : ℕᵒᵖ ⥤ 𝒟) :
    F.lan.obj (seqHomColim M) ≅ seqHomColim (M ⋙ F) where
  hom := lanSeqHomColimHom F M
  inv := lanSeqHomColimInv F M
  hom_inv_id := by
    refine Functor.hom_ext_of_isLeftKanExtension _ (F.lanUnit.app (seqHomColim M)) _ _ ?_
    rw [Functor.whiskerLeft_comp, ← Category.assoc, lanUnit_comp_lanSeqHomColimHom,
      Functor.whiskerLeft_id', Category.comp_id]
    refine colimit.hom_ext fun ⟨⟨n⟩⟩ => ?_
    rw [ι_eq_coyonedaEquiv_symm, coyonedaEquiv_symm_comp, coyonedaEquiv_symm_comp]
    congr 1
    change (lanSeqHomColimInv F M).app _ ((seqHomColimToComp F M).app _ _) = _
    rw [seqHomColimToComp_app_seqStage, F.map_id]
    exact lanSeqHomColimInv_app_seqStage_id F M n
  inv_hom_id := by
    refine colimit.hom_ext fun ⟨⟨n⟩⟩ => ?_
    rw [Category.comp_id, ι_eq_coyonedaEquiv_symm, coyonedaEquiv_symm_comp]
    congr 1
    change (lanSeqHomColimHom F M).app _ ((lanSeqHomColimInv F M).app _ _) = _
    refine (congrArg _ (lanSeqHomColimInv_app_seqStage_id F M n)).trans ?_
    change ((F.lanUnit.app (seqHomColim M)) ≫
      Functor.whiskerLeft F (lanSeqHomColimHom F M)).app _ _ = _
    rw [lanUnit_comp_lanSeqHomColimHom, seqHomColimToComp_app_seqStage, F.map_id]
    rfl

/-- The inverse of `Pro.lanSeqHomColimIso` sends the class of `h : F M_n ⟶ L` to the image under
`h` of the unit at the class of the identity of `M_n`. -/
public lemma lanSeqHomColimIso_inv_app_seqStage (M : ℕᵒᵖ ⥤ 𝒟) {L : 𝒟'} {n : ℕ}
    (h : F.obj (M.obj (op n)) ⟶ L) :
    (lanSeqHomColimIso F M).inv.app L (seqStage (M ⋙ F) h) =
      (F.lan.obj (seqHomColim M)).map h
        ((F.lanUnit.app (seqHomColim M)).app (M.obj (op n)) (seqStage M (𝟙 (M.obj (op n))))) := by
  rw [← seqHomColim_map_seqStage_id (M ⋙ F) h, NatTrans.naturality_apply]
  exact congrArg _ (lanSeqHomColimInv_app_seqStage_id F M n)

end Pro

/-- The left Kan extension along `F` of the functor of points of a pro-object is again the
functor of points of a pro-object, namely of the termwise image sequence. -/
public lemma isSequentialProObject_lan [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A]
    {A : 𝒟 ⥤ Type v} (hA : IsSequentialProObject 𝒟 A) :
    IsSequentialProObject 𝒟' (F.lan.obj A) := by
  obtain ⟨M, ⟨e⟩⟩ := hA
  exact ⟨M ⋙ F, ⟨F.lan.mapIso (e ≪≫ Pro.seqHomColimIso M) ≪≫ Pro.lanSeqHomColimIso F M ≪≫
    (Pro.seqHomColimIso (M ⋙ F)).symm⟩⟩

namespace ProSeq

variable [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A]

/-- **Pushforward of pro-objects along a functor.** The functor `Pro-𝒟 ⥤ Pro-𝒟'` applying `F`
termwise to inverse sequences. It is defined on functors of points, where it is the left Kan
extension along `F`; that it is the termwise image is `CategoryTheory.ProSeq.mapOfIso`. -/
public def map : ProSeq 𝒟 ⥤ ProSeq 𝒟' :=
  (ObjectProperty.lift (IsSequentialProObject 𝒟')
    ((IsSequentialProObject 𝒟).ι ⋙ F.lan)
    (fun P => isSequentialProObject_lan F P.property)).op

/-- The functor of points of `ProSeq.map F P` is the left Kan extension along `F` of the functor
of points of `P`. -/
public lemma points_map_obj (P : ProSeq 𝒟) : ((map F).obj P).points = F.lan.obj P.points :=
  rfl

/-- `ProSeq.map F` sends the pro-object of `(M_n)` to the pro-object of `(F M_n)`. -/
public def mapOfIso (M : ℕᵒᵖ ⥤ 𝒟) : (map F).obj (of M) ≅ of (M ⋙ F) :=
  (ObjectProperty.isoMk _ (Pro.seqHomColimIso (M ⋙ F) ≪≫ (Pro.lanSeqHomColimIso F M).symm ≪≫
    F.lan.mapIso (Pro.seqHomColimIso M).symm)).op

end ProSeq

end Map

/-! ### Functoriality of the pushforward in the functor -/

section MapFunctoriality

/-- Left Kan extension along a composite is the composite of the left Kan extensions: both are left
adjoint to precomposition with `G ⋙ H`. -/
public def _root_.CategoryTheory.Functor.lanCompIso {𝒟'' : Type w₁} [Category.{v} 𝒟'']
    (T : Type w₂) [Category T] (G : 𝒟 ⥤ 𝒟') (H : 𝒟' ⥤ 𝒟'')
    [∀ A : 𝒟 ⥤ T, G.HasLeftKanExtension A] [∀ A : 𝒟' ⥤ T, H.HasLeftKanExtension A]
    [∀ A : 𝒟 ⥤ T, (G ⋙ H).HasLeftKanExtension A] :
    G.lan (H := T) ⋙ H.lan ≅ (G ⋙ H).lan :=
  Adjunction.leftAdjointUniq ((G.lanAdjunction T).comp (H.lanAdjunction T))
    (((G ⋙ H).lanAdjunction T).ofNatIsoRight
      (NatIso.ofComponents (fun B => Functor.associator G H B) (fun _ => by ext; simp)))

/-- Left Kan extensions along isomorphic functors are isomorphic: both are left adjoint to
precomposition with the same functor, up to the isomorphism. -/
public def _root_.CategoryTheory.Functor.lanIsoOfIso (T : Type w₂) [Category T] {G G' : 𝒟 ⥤ 𝒟'}
    (e : G ≅ G') [∀ A : 𝒟 ⥤ T, G.HasLeftKanExtension A]
    [∀ A : 𝒟 ⥤ T, G'.HasLeftKanExtension A] : G.lan (H := T) ≅ G'.lan :=
  Adjunction.leftAdjointUniq (G.lanAdjunction T)
    ((G'.lanAdjunction T).ofNatIsoRight ((Functor.whiskeringLeft 𝒟 𝒟' T).mapIso e).symm)

namespace ProSeq

/-- An isomorphism of functors on functors of points, between functors preserving functors of
points of pro-objects, is an isomorphism of the induced functors on pro-objects. -/
public def liftOpIso {Φ Ψ : (𝒟 ⥤ Type v) ⥤ (𝒟' ⥤ Type v)}
    (hΦ : ∀ P : (IsSequentialProObject 𝒟).FullSubcategory,
      IsSequentialProObject 𝒟' (((IsSequentialProObject 𝒟).ι ⋙ Φ).obj P))
    (hΨ : ∀ P : (IsSequentialProObject 𝒟).FullSubcategory,
      IsSequentialProObject 𝒟' (((IsSequentialProObject 𝒟).ι ⋙ Ψ).obj P)) (e : Φ ≅ Ψ) :
    (ObjectProperty.lift (IsSequentialProObject 𝒟') ((IsSequentialProObject 𝒟).ι ⋙ Φ) hΦ).op ≅
      (ObjectProperty.lift (IsSequentialProObject 𝒟') ((IsSequentialProObject 𝒟).ι ⋙ Ψ) hΨ).op :=
  NatIso.op (liftIso hΨ hΦ (Functor.isoWhiskerLeft (IsSequentialProObject 𝒟).ι e.symm))

/-- Pushing forward along `G` and then along `H` is pushing forward along `G ⋙ H`. -/
public def mapComp {𝒟'' : Type w₁} [Category.{v} 𝒟''] (G : 𝒟 ⥤ 𝒟') (H : 𝒟' ⥤ 𝒟'')
    [∀ A : 𝒟 ⥤ Type v, G.HasLeftKanExtension A] [∀ A : 𝒟' ⥤ Type v, H.HasLeftKanExtension A]
    [∀ A : 𝒟 ⥤ Type v, (G ⋙ H).HasLeftKanExtension A] :
    map G ⋙ map H ≅ map (G ⋙ H) :=
  liftOpIso (Φ := G.lan ⋙ H.lan) (Ψ := (G ⋙ H).lan) (fun P => isSequentialProObject_lan H
      (isSequentialProObject_lan G P.property))
    (fun P => isSequentialProObject_lan (G ⋙ H) P.property) (Functor.lanCompIso (Type v) G H)

/-- Isomorphic functors induce isomorphic pushforwards of pro-objects. -/
public def mapIsoOfIso {G G' : 𝒟 ⥤ 𝒟'} (e : G ≅ G')
    [∀ A : 𝒟 ⥤ Type v, G.HasLeftKanExtension A] [∀ A : 𝒟 ⥤ Type v, G'.HasLeftKanExtension A] :
    map G ≅ map G' :=
  liftOpIso (fun P => isSequentialProObject_lan G P.property)
    (fun P => isSequentialProObject_lan G' P.property) (Functor.lanIsoOfIso (Type v) e)

end ProSeq

end MapFunctoriality

end CategoryTheory

end
