module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproductSheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Evaluation of the extension along a change of base scheme (Stacks 03I4 (1))

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `j` be the corresponding localization
functor from the big fppf site of `S` to that of `S'`. For a sheaf `F` on the site of `S` and a
scheme `T'` over `S'`, Stacks 03I4 part (1) evaluates the extension by
`j_!F(T'/S') = ∐_{φ : T' ⟶ S} F(T' →φ S)`, the coproduct over the factorizations of the structure
morphism of `T'` through `S`.

The right-hand side is `CategoryTheory.OverShriek.relocalizePresheafFunctor g`, so the content of
the lemma is that the canonical comparison map out of that presheaf is an isomorphism; stating it
that way records the identification naturally in `T'`, rather than as a bijection for each `T'`
separately.

## Main results

* `AlgebraicGeometry.isIso_relocalizeOfRestricted`: **Stacks 03I4 (1)**.

## Implementation notes

The extension functor is taken to be an arbitrary left adjoint `L` of restriction along
`CategoryTheory.Over.map g`, since adjoints are unique up to canonical isomorphism; the claim is
that the map `OverShriek.relocalizeOfRestricted g` obtained from the unit of that adjunction by the
presheaf-level adjunction `CategoryTheory.OverShriek.relocalizeAdjunction` is an isomorphism.

The proof does not sheafify. The presheaf `relocalizePresheafFunctor g |>.obj F` is already a
sheaf: it is isomorphic to the coproduct presheaf of Stacks 03CD for the twice-localized site
`(Sch/S')/(S → S')`, whose sheaf condition is `CategoryTheory.OverShriek.isSheaf_presheaf`
together with subcanonicity of the big fppf topology
(`AlgebraicGeometry.BigFppfSite.subcanonical_topology`). Being a sheaf, it is a candidate value of
`L`, and the comparison map is an isomorphism because the corresponding map of sheaves is inverse
to the one produced by the universal property of `L` — a two-line calculation with
`CategoryTheory.OverShriek.relocalizeToRestricted_relocalizeOfRestricted`.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The sections of the coproduct presheaf of Stacks 03CD for the twice-localized site
`(Sch/S')/(S → S')` over an `S'`-scheme `A` are the pairs of a factorization `A.left ⟶ S` of the
structure morphism of `A` and a section of `F` over it: the sections of
`CategoryTheory.OverShriek.relocalizePresheafFunctor g |>.obj F` over `A`. -/
private def relocalizeCoproductEquiv
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (F : Sheaf (B.topology.over S) (Type u))
    [hcont : ((Over.mk g).iteratedSliceForward).IsContinuous
      ((B.topology.over S').over (Over.mk g)) (B.topology.over S)]
    (A : Over S') :
    (OverShriek.presheaf (U := Over.mk g)
      (((Over.mk g).iteratedSliceForward.sheafPushforwardContinuous (Type u)
        ((B.topology.over S').over (Over.mk g)) (B.topology.over S)).obj F).obj).obj (op A) ≃
      ((OverShriek.relocalizePresheafFunctor g).obj F.obj).obj (op A) := by
  dsimp [OverShriek.presheaf, OverShriek.relocalizePresheafFunctor,
    OverShriek.fiberFunctor, OverShriek.fiber, OverShriek.presheafFunctorToOver,
    OverShriek.presheafToYoneda]
  change (Σ φ : A ⟶ Over.mk g, F.obj.obj (op (Over.mk φ.left))) ≃
    {p : Σ ψ : A.left ⟶ S, F.obj.obj (op (Over.mk ψ)) // p.1 ≫ g = A.hom}
  exact {
    toFun := fun x => ⟨⟨x.1.left, x.2⟩, x.1.w⟩
    invFun := fun x => ⟨Over.homMk x.1.1 x.2, x.1.2⟩
    left_inv := by
      rintro ⟨φ, s⟩
      congr 1
    right_inv := by
      rintro ⟨⟨ψ, s⟩, h⟩
      apply Subtype.ext
      congr 1 }

/-- `AlgebraicGeometry.relocalizeCoproductEquiv`, as an isomorphism of presheaves on the big fppf
site of `S'`. -/
private def relocalizeCoproductIso
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (F : Sheaf (B.topology.over S) (Type u))
    [hcont : ((Over.mk g).iteratedSliceForward).IsContinuous
      ((B.topology.over S').over (Over.mk g)) (B.topology.over S)] :
    OverShriek.presheaf (U := Over.mk g)
      (((Over.mk g).iteratedSliceForward.sheafPushforwardContinuous (Type u)
        ((B.topology.over S').over (Over.mk g)) (B.topology.over S)).obj F).obj ≅
      (OverShriek.relocalizePresheafFunctor g).obj F.obj :=
  NatIso.ofComponents (fun A => (relocalizeCoproductEquiv B S S' g F A.unop).toIso)
    (by
      intro A A' f
      ext p
      rcases p with ⟨φ, s⟩
      rfl)

/-- **Stacks 03I4 (1).** For a morphism `g : S ⟶ S'` of a big fppf site and a sheaf `F` on the big
fppf site of `S`, the canonical map from the presheaf of pairs of a factorization `T' → S → S'` and
a section of `F` over it to the extension `j_!F` is an isomorphism. -/
@[stacks 03I4 "extension_evaluation"]
theorem isIso_relocalizeOfRestricted
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous (Type u)
      (B.topology.over S) (B.topology.over S'))
    (F : Sheaf (B.topology.over S) (Type u)) :
    IsIso (OverShriek.relocalizeOfRestricted g (adj.unit.app F).hom) := by
  classical
  let U : Over S' := Over.mk g
  let J := B.topology.over S'
  let K := J.over U
  let _ : U.iteratedSliceForward.IsContinuous K (B.topology.over S) :=
    show (Over.mk g).iteratedSliceForward.IsContinuous
      ((B.topology.over S').over (Over.mk g)) (B.topology.over (Over.mk g).left) from inferInstance
  let G : Sheaf K (Type u) :=
    (U.iteratedSliceForward.sheafPushforwardContinuous (Type u) K
      (B.topology.over S)).obj F
  have hU : Presieve.IsSheaf J (yoneda.obj U) := by
    let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
    let _ : J.Subcanonical := inferInstance
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj U)
  let P := (OverShriek.relocalizePresheafFunctor g).obj F.obj
  have hP : Presheaf.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type J P).2 <|
      Presieve.isSheaf_iso J (relocalizeCoproductIso B S S' g F) <|
        OverShriek.isSheaf_presheaf J G.obj hU ((isSheaf_iff_isSheaf_of_type K G.obj).1 G.property)
  let ShP : Sheaf J (Type u) := ⟨P, hP⟩
  let R := (Over.map g).sheafPushforwardContinuous (Type u)
    (B.topology.over S) (B.topology.over S')
  let β : F.obj ⟶ (OverShriek.relocalizeRestrict g).obj ((L.obj F).obj) := (adj.unit.app F).hom
  let a : ShP ⟶ L.obj F :=
    ObjectProperty.homMk (OverShriek.relocalizeOfRestricted g β)
  let u' : F ⟶ R.obj ShP :=
    ObjectProperty.homMk ((OverShriek.relocalizeAdjunction g).unit.app F.obj)
  let b : L.obj F ⟶ ShP := (adj.homEquiv F ShP).symm u'
  have hbdef : (adj.homEquiv F ShP) b = u' := (adj.homEquiv F ShP).apply_symm_apply u'
  have hb : β ≫ Functor.whiskerLeft (Over.map g).op b.hom =
      (OverShriek.relocalizeAdjunction g).unit.app F.obj := by
    have h := hbdef
    rw [Adjunction.homEquiv_unit] at h
    exact Sheaf.hom_ext_iff.1 h
  have hβ : OverShriek.relocalizeToRestricted g (OverShriek.relocalizeOfRestricted g β) = β :=
    OverShriek.relocalizeToRestricted_relocalizeOfRestricted g _
  have hu : u' ≫ R.map a = adj.unit.app F := Sheaf.hom_ext hβ
  refine (ObjectProperty.isIso_hom_iff a).2 ⟨b, ?_, ?_⟩
  · refine Sheaf.hom_ext ?_
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
    refine (OverShriek.relocalizeAdjunction g).homEquiv F.obj ShP.obj |>.injective ?_
    rw [(OverShriek.relocalizeAdjunction g).homEquiv_naturality_right,
      (OverShriek.relocalizeAdjunction g).homEquiv_id]
    show OverShriek.relocalizeToRestricted g
        (OverShriek.relocalizeOfRestricted g β) ≫
          Functor.whiskerLeft (Over.map g).op b.hom = _
    rw [hβ]
    exact hb
  · refine (adj.homEquiv F (L.obj F)).injective ?_
    rw [adj.homEquiv_id, adj.homEquiv_naturality_right, hbdef]
    exact hu

end AlgebraicGeometry

end
