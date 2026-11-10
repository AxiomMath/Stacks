module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Change of base scheme for sheaves on a big fppf site

Let `g : S ⟶ S'` be a morphism of a big fppf site. Relocalization along `g` is the functor
`CategoryTheory.Over.map g` between the slices, and it is continuous for the localized
topologies, so it induces restriction of sheaves from the site over `S'` to the site over
`S` and, as its left adjoint, extension in the other direction. This file records how the
three operations act on representable sheaves and how a restricted sheaf is evaluated.

## Main results

* `AlgebraicGeometry.Space.extend_representable`: extension along `g` carries a sheaf
  represented by `X / S` to one represented by the same scheme viewed over `S'`.
* `AlgebraicGeometry.Space.restrict_representable`: restriction along `g` carries a sheaf
  represented by `X' / S'` to one represented by the fibre product `S ×_{S'} X' / S`.
* `AlgebraicGeometry.Space.restrict_eval`: a restricted sheaf is evaluated at `T / S` by
  evaluating the original sheaf at `T / S'`.
* `CategoryTheory.OverShriek.isSheaf_relocalizePresheafFunctor_obj`: the presheaf-level
  relocalization of a sheaf is a sheaf, on any site whose localization at `S / S'` has a
  representable sheaf `h_{S/S'}`.
* `CategoryTheory.OverShriek.isIso_relocalizeOfRestricted_unit`: consequently the presheaf-level
  relocalization computes the extension `L` itself.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relocalize`: the extension of an algebraic space
  over `S` along `g` is an algebraic space over `S'`, in the presheaf-level form.
* `AlgebraicGeometry.Space.isPullback_relocalize_atlas`: the extended atlas has the extended
  kernel pair.
* `AlgebraicGeometry.isIso_relocalizeOfRestricted` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ExtensionEvaluation.lean`: the canonical map from the
  presheaf of factorizations to the extension of a sheaf is an isomorphism, for the big fppf
  site.
* `AlgebraicGeometry.Space.exists_extended_presentation`: an étale presentation `U / R` of an
  algebraic space over `S` extends to the presentation of the extension by the images of `U` and
  `R` over `S'`, whose atlas is again a coequalizer of its kernel pair in sheaves.

## Implementation notes

Representability of a sheaf is recorded by an isomorphism of its underlying presheaf with a
Yoneda presheaf, together with the representing object. Stating it this way rather than
through `CategoryTheory.Functor.IsRepresentable` keeps the representing object specified,
which is what the two results actually produce, and it means neither statement has to carry
a separately chosen subcanonical structure on the site.

Subcanonicity of the big fppf topology is nevertheless needed inside the proof of the
extension statement, to know that the target Yoneda presheaf is a sheaf. It is supplied by
`AlgebraicGeometry.BigFppfSite.subcanonical_topology`.

The extension is taken to be an arbitrary left adjoint of restriction rather than a chosen
one; left adjoints are unique up to canonical isomorphism, so the statement is about any of
them. The proof identifies the corepresenting object of `L.obj F` by hand, through the
Yoneda lemma for sheaves, rather than invoking a formula for the extension.

Part (3) is proved at the level of presheaves, for the presheaf-level relocalization
`CategoryTheory.OverShriek.relocalizePresheafFunctor` — written `Λ` in
`StacksFrontier/CategoryTheory/Sites/Localization/RelocalizeRepresentable.lean` — and then
transported to `L`. That is the right place for it: `Λ` is a left adjoint of restriction on
presheaves, it preserves connected limits and representables, and it carries a sheaf to a sheaf,
so no sheafification intervenes and the three clauses of Stacks 025Y can be checked directly. The
transport is the identification of `Λ F` with `L F`, which is the relocalization analogue of
Stacks 03HT and holds for exactly the same reason: both corepresent maps out of `F` restricted
along `Over.map g`. The presheaf-level form is also the one the absolute separation properties
need, since `AlgebraicGeometry.Space.viewOverIntegers` is defined by `Λ`.

That `Λ G` is a sheaf is the only new input. It is obtained by recognising `Λ G` as the coproduct
presheaf of Stacks 03CD for the localization of the site over `S'` at the object `S / S'`: a
section over `A / S'` is a morphism `A ⟶ (S --g--> S')` together with a section of `G` over its
underlying morphism to `S`. The sheaf condition for that coproduct presheaf is
`CategoryTheory.OverShriek.isSheaf_presheaf`, whose two hypotheses are that `h_{S/S'}` is a sheaf
— here subcanonicity of the big fppf topology again — and that `G` pulled back to the iterated
slice is a sheaf, which holds because the iterated slice comparison is continuous.

The extension of a presentation is read off from the same identification of `L` with `Λ`, made into
an isomorphism `Λ F ≅ L F` natural in `F`: naturality is the transpose of the naturality of the
unit of `adj` under the presheaf-level adjunction `Λ ⊣ j^{-1}`. The extended atlas is then the
image under `Λ` of the original one, read through `Λ h_U ≅ h_{j U}` and transported along that
isomorphism. Its kernel pair is `AlgebraicGeometry.Space.isPullback_relocalize_atlas`; its two
projections are an étale equivalence relation by Stacks 0262 part (1) applied to the extended
kernel pair, `j = Over.map g` leaving the underlying morphisms of schemes — hence their étaleness —
unchanged; it is surjective and étale by the same transport as in
`AlgebraicGeometry.Space.isAlgebraicSpace_relocalize`; and it is a coequalizer because `L`, a left
adjoint, preserves the coequalizer which Stacks 0262 part (3) provides over `S`.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace Space

/-- **Stacks 03I4.** Extension along `g : S ⟶ S'` carries a sheaf represented by `X / S` to
one represented by `X / S'`. -/
@[stacks 03I4 "extension_representable"]
theorem extend_representable
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤ Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous (Type u)
      (B.topology.over S) (B.topology.over S'))
    (X : Over S) (F : Sheaf (B.topology.over S) (Type u))
    (hF : Nonempty (F.obj ≅ yoneda.obj X)) :
    Nonempty (((L.obj F).obj) ≅ yoneda.obj ((Over.map g).obj X)) := by
  classical
  let u₀ := Over.map g
  let J := B.topology.over S
  let K := B.topology.over S'
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstance
  let _ : K.Subcanonical := inferInstance
  let _ : u₀.IsContinuous J K := inferInstance
  let eF : F ≅ J.yoneda.obj X :=
    (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf J (Type u))).preimageIso
      (Classical.choice hF)
  let R := u₀.sheafPushforwardContinuous (Type u) J K
  let lhsEquiv (G : Sheaf K (Type u)) :
      (L.obj F ⟶ G) ≃ G.obj.obj (Opposite.op (u₀.obj X)) := by
    let eHom : (F ⟶ R.obj G) ≃ (J.yoneda.obj X ⟶ R.obj G) :=
      { toFun f := eF.inv ≫ f
        invFun f := eF.hom ≫ f
        left_inv f := by simp
        right_inv f := by simp }
    simpa [R, Functor.sheafPushforwardContinuous] using
      (adj.homEquiv _ _).trans (eHom.trans (J.yonedaEquiv))
  have lhs_naturality (G G' : Sheaf K (Type u)) (α : G ⟶ G') (f : L.obj F ⟶ G) :
      lhsEquiv G' (f ≫ α) = α.hom.app (Opposite.op (u₀.obj X)) (lhsEquiv G f) := by
    change J.yonedaEquiv (eF.inv ≫ (adj.homEquiv F G') (f ≫ α)) =
      α.hom.app (Opposite.op (u₀.obj X))
        (J.yonedaEquiv (eF.inv ≫ (adj.homEquiv F G) f))
    rw [Adjunction.homEquiv_naturality_right, ← Category.assoc, J.yonedaEquiv_comp]
    rfl
  let η : coyoneda.obj (Opposite.op (L.obj F)) ≅
      coyoneda.obj (Opposite.op (K.yoneda.obj (u₀.obj X))) :=
    NatIso.ofComponents
      (fun G => Equiv.toIso ((lhsEquiv G).trans (K.yonedaEquiv).symm))
      (by
        intro G G' α
        ext f
        change (K.yonedaEquiv).symm (lhsEquiv G' (f ≫ α)) =
          (K.yonedaEquiv).symm (lhsEquiv G f) ≫ α
        apply (K.yonedaEquiv).injective
        rw [Equiv.apply_symm_apply, lhs_naturality, K.yonedaEquiv_comp,
          Equiv.apply_symm_apply])
  let e : L.obj F ≅ K.yoneda.obj (u₀.obj X) :=
    ((Coyoneda.fullyFaithful (C := Sheaf K (Type u))).preimageIso η).unop.symm
  exact ⟨(sheafToPresheaf K (Type u)).mapIso e⟩

/-- **Stacks 03I4.** Restricting a sheaf represented by `X' / S'` along `g : S ⟶ S'` gives a
sheaf represented by the fibre product `S ×_{S'} X' / S`. -/
@[stacks 03I4 "restriction_representable"]
theorem restrict_representable
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (X' : BigFppfOver B S' hS')
    (F' : Sheaf (BigFppfOver.topology B S' hS') (Type u))
    (hF' : Nonempty (F'.obj ≅ yoneda.obj X')) :
    ∃ (Xbase : BigFppfOver B S hS)
      (p : Xbase.left ⟶ X'.left),
        IsPullback (B.inclusion.map p) (B.inclusion.map Xbase.hom)
          (B.inclusion.map X'.hom) (B.inclusion.map g) ∧
          Nonempty
            (((((Over.map g).sheafPushforwardContinuous (Type u)
              (B.topology.over (B.obj hS)) (B.topology.over (B.obj hS'))).obj F').obj) ≅
                yoneda.obj Xbase) := by
  let Xbase : BigFppfOver B S hS := (Over.pullback g).obj X'
  refine ⟨Xbase, pullback.fst X'.hom g, ?_, ?_⟩
  · change IsPullback (B.inclusion.map (pullback.fst X'.hom g))
      (B.inclusion.map (pullback.snd X'.hom g)) (B.inclusion.map X'.hom)
      (B.inclusion.map g)
    exact IsPullback.map B.inclusion (IsPullback.of_hasPullback X'.hom g)
  · refine ⟨?_⟩
    change (Over.map g).op ⋙ F'.obj ≅ yoneda.obj Xbase
    exact (((Functor.whiskeringLeft _ _ _).obj (Over.map g).op).mapIso hF'.some).trans
      ((Over.mapPullbackAdj g).representableBy X').toIso.symm

/-- **Stacks 03I4, part (4): evaluation of a restricted sheaf.** Let `g : S ⟶ S'` be a morphism of
a big fppf site, let `j = Over.map g` be the associated localization functor and let `F'` be a
sheaf on the big fppf site over `S'`. For an object `T / S`, the sections of `j^{-1}F'` over
`T / S` are the sections of `F'` over `T / S'`, that is over `T` with structure morphism the
composite `T ⟶ S ⟶ S'`.

Restriction along a continuous functor is precomposition, so this is the instance of
`CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj` for `j`; it is recorded here to
state the clause for the big fppf site, with `T / S'` written as the composite structure
morphism. -/
@[stacks 03I4 "restriction_evaluation"]
theorem restrict_eval
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F' : Sheaf (BigFppfOver.topology B S' hS') (Type u))
    (T : BigFppfOver B S hS) :
    (((Over.map g).sheafPushforwardContinuous (Type u)
        (B.topology.over (B.obj hS)) (B.topology.over (B.obj hS'))).obj F').obj.obj
          (Opposite.op T) = F'.obj.obj (Opposite.op (Over.mk (T.hom ≫ g))) :=
  Functor.sheafPushforwardContinuous_obj_obj_obj (Over.map g) (Type u)
    (B.topology.over (B.obj hS)) (B.topology.over (B.obj hS')) F' (Opposite.op T)

end Space

end AlgebraicGeometry

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {S S' : C} (g : S ⟶ S')

/-- The transpose `Λ G ⟶ F` of `β : G ⟶ j^{-1}F` is natural in `G`: precomposing with `Λ φ` is
transposing `φ ≫ β`.  This is the left naturality of `relocalizeAdjunction`. -/
private theorem map_comp_relocalizeOfRestricted {G G' : (Over S)ᵒᵖ ⥤ Type v}
    {F : (Over S')ᵒᵖ ⥤ Type v} (φ : G' ⟶ G) (β : G ⟶ (relocalizeRestrict g).obj F) :
    (relocalizePresheafFunctor g).map φ ≫ relocalizeOfRestricted g β =
      relocalizeOfRestricted g (φ ≫ β) :=
  ((relocalizeAdjunction g).homEquiv_naturality_left_symm φ β).symm

/-- The transpose `Λ G ⟶ F` of `β : G ⟶ j^{-1}F` is natural in `F`: postcomposing with `γ` is
transposing `β ≫ j^{-1}γ`.  This is the right naturality of `relocalizeAdjunction`. -/
private theorem relocalizeOfRestricted_comp {G : (Over S)ᵒᵖ ⥤ Type v}
    {F F' : (Over S')ᵒᵖ ⥤ Type v} (β : G ⟶ (relocalizeRestrict g).obj F) (γ : F ⟶ F') :
    relocalizeOfRestricted g β ≫ γ =
      relocalizeOfRestricted g (β ≫ (relocalizeRestrict g).map γ) :=
  ((relocalizeAdjunction g).homEquiv_naturality_right_symm β γ).symm

/-- Sections of `Λ G` over `A / S'` are pairs consisting of a morphism `A ⟶ (S --g--> S')` of
`C/S'` and a section of `G` over its underlying morphism `A.left ⟶ S`; that is, `Λ G` is the
coproduct presheaf of Stacks 03CD for the localization of `C/S'` at the object `S/S'`. -/
private def relocalizeCoproductEquiv (G : (Over S)ᵒᵖ ⥤ Type v) (A : Over S') :
    (presheaf (U := Over.mk g)
        ((Over.mk g).iteratedSliceForward.op ⋙ G)).obj (Opposite.op A) ≃
      ((relocalizePresheafFunctor g).obj G).obj (Opposite.op A) := by
  dsimp [presheaf, relocalizePresheafFunctor, fiberFunctor, fiber, presheafFunctorToOver,
    presheafToYoneda]
  change (Σ φ : A ⟶ Over.mk g, G.obj (Opposite.op (Over.mk φ.left))) ≃
    {p : Σ ψ : A.left ⟶ S, G.obj (Opposite.op (Over.mk ψ)) // p.1 ≫ g = A.hom}
  exact
    { toFun := fun x => ⟨⟨x.1.left, x.2⟩, x.1.w⟩
      invFun := fun x => ⟨Over.homMk x.1.1 x.2, x.1.2⟩
      left_inv := by
        rintro ⟨φ, s⟩
        congr 1
      right_inv := by
        rintro ⟨⟨ψ, s⟩, h⟩
        apply Subtype.ext
        congr 1 }

/-- `relocalizeCoproductEquiv`, as an isomorphism of presheaves on `C/S'`. -/
private def relocalizeCoproductIso (G : (Over S)ᵒᵖ ⥤ Type v) :
    presheaf (U := Over.mk g) ((Over.mk g).iteratedSliceForward.op ⋙ G) ≅
      (relocalizePresheafFunctor g).obj G :=
  NatIso.ofComponents (fun A => (relocalizeCoproductEquiv g G A.unop).toIso)
    (by intro A A' f; ext p; rcases p with ⟨φ, s⟩; rfl)

/-- **The presheaf-level relocalization of a sheaf is a sheaf.**  If `h_{(S --g--> S')}` is a
sheaf on the localized site `C/S'` — for instance because the topology is subcanonical — and `G`
is a sheaf on `C/S`, then `Λ G` is a sheaf on `C/S'`.

Under `relocalizeCoproductIso`, `Λ G` is the coproduct presheaf of Stacks 03CD for the
localization of `C/S'` at `S/S'`, whose sheaf condition is
`CategoryTheory.OverShriek.isSheaf_presheaf`; the restriction of `G` to the iterated slice is a
sheaf because the iterated slice comparison is continuous. -/
@[sga "3 IV 4.5.2" "Sheaf clause"]
theorem isSheaf_relocalizePresheafFunctor_obj (J : GrothendieckTopology C)
    (G : (Over S)ᵒᵖ ⥤ Type v)
    (hg : Presieve.IsSheaf (J.over S') (yoneda.obj (Over.mk g)))
    (hG : Presheaf.IsSheaf (J.over S) G) :
    Presheaf.IsSheaf (J.over S') ((relocalizePresheafFunctor g).obj G) := by
  have _ : (Over.mk g).iteratedSliceForward.IsContinuous
      ((J.over S').over (Over.mk g)) (J.over S) :=
    show (Over.mk g).iteratedSliceForward.IsContinuous
      ((J.over S').over (Over.mk g)) (J.over (Over.mk g).left) from inferInstance
  have hG' : Presheaf.IsSheaf ((J.over S').over (Over.mk g))
      ((Over.mk g).iteratedSliceForward.op ⋙ G) :=
    (Over.mk g).iteratedSliceForward.op_comp_isSheaf
      ((J.over S').over (Over.mk g)) (J.over S) ⟨G, hG⟩
  exact (Presheaf.isSheaf_of_iso_iff (relocalizeCoproductIso g G)).1
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_presheaf (J.over S') _ hg ((isSheaf_iff_isSheaf_of_type _ _).1 hG')))

/-- **The presheaf-level relocalization computes the sheaf-level `j_!`.**  Let `L` be a left
adjoint of restriction along `j = Over.map g`, and suppose the presheaf-level relocalization `Λ`
carries sheaves on `C/S` to sheaves on `C/S'`.  Then the canonical map `Λ F ⟶ L F` transposing
the unit of the adjunction is an isomorphism: a section of `L F` over `A / S'` is a factorization
`A.left ⟶ S ⟶ S'` of the structure morphism together with a section of `F` over it.

This is the relocalization analogue of
`CategoryTheory.OverShriek.isIso_ofRestricted_unit` (Stacks 03HT), proved the same way: `Λ F` and
`L F` corepresent the same functor on sheaves over `S'`, the first by `relocalizeAdjunction` and
the second by `adj`. -/
@[sga "4 III 1.7" "Clause 1, special case"]
theorem isIso_relocalizeOfRestricted_unit (J : GrothendieckTopology C)
    (hP : ∀ G : Sheaf (J.over S) (Type v),
      Presheaf.IsSheaf (J.over S') ((relocalizePresheafFunctor g).obj G.obj))
    {L : Sheaf (J.over S) (Type v) ⥤ Sheaf (J.over S') (Type v)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous (Type v) (J.over S) (J.over S'))
    (F : Sheaf (J.over S) (Type v)) :
    IsIso (relocalizeOfRestricted g (F := (L.obj F).obj)
      (show F.obj ⟶ (relocalizeRestrict g).obj ((L.obj F).obj) from (adj.unit.app F).hom)) := by
  let R := (Over.map g).sheafPushforwardContinuous (Type v) (J.over S) (J.over S')
  let ShP : Sheaf (J.over S') (Type v) := ⟨(relocalizePresheafFunctor g).obj F.obj, hP F⟩
  let β : F.obj ⟶ (relocalizeRestrict g).obj ((L.obj F).obj) := (adj.unit.app F).hom
  let a : ShP ⟶ L.obj F := ObjectProperty.homMk (relocalizeOfRestricted g β)
  let u' : F ⟶ R.obj ShP := ObjectProperty.homMk ((relocalizeAdjunction g).unit.app F.obj)
  let b : L.obj F ⟶ ShP := (adj.homEquiv F ShP).symm u'
  have hb : β ≫ Functor.whiskerLeft (Over.map g).op b.hom =
      (relocalizeAdjunction g).unit.app F.obj := by
    have h := (adj.homEquiv F ShP).apply_symm_apply u'
    rw [Adjunction.homEquiv_unit] at h
    exact Sheaf.hom_ext_iff.1 h
  have hu : u' ≫ R.map a = adj.unit.app F := by
    refine Sheaf.hom_ext ?_
    change relocalizeToRestricted g (relocalizeOfRestricted g β) = β
    exact relocalizeToRestricted_relocalizeOfRestricted g _
  refine (ObjectProperty.isIso_hom_iff a).2 ⟨b, ?_, ?_⟩
  · refine Sheaf.hom_ext ?_
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
    refine ((relocalizeAdjunction g).homEquiv F.obj ShP.obj).injective ?_
    rw [(relocalizeAdjunction g).homEquiv_naturality_right,
      (relocalizeAdjunction g).homEquiv_id]
    change relocalizeToRestricted g (relocalizeOfRestricted g β) ≫
      Functor.whiskerLeft (Over.map g).op b.hom = _
    rw [relocalizeToRestricted_relocalizeOfRestricted]
    exact hb
  · have hbdef : (adj.homEquiv F ShP) b = u' := (adj.homEquiv F ShP).apply_symm_apply u'
    refine (adj.homEquiv F (L.obj F)).injective ?_
    rw [adj.homEquiv_id, adj.homEquiv_naturality_right, hbdef]
    exact hu

end CategoryTheory.OverShriek

namespace AlgebraicGeometry

open CategoryTheory.OverShriek

namespace Space

/-- The presheaf-level relocalization of a sheaf on the big fppf site over `S` is a sheaf on the
big fppf site over `S'`, the topology of the site being subcanonical
(`AlgebraicGeometry.BigFppfSite.subcanonical_topology`). -/
theorem isSheaf_relocalize (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B (B.inclusion.obj S) S.property) F) :
    Presheaf.IsSheaf (BigFppfOver.topology B (B.inclusion.obj S') S'.property)
      ((relocalizePresheafFunctor g).obj F) := by
  have _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  have _ : (B.topology.over S').Subcanonical := inferInstance
  exact isSheaf_relocalizePresheafFunctor_obj g B.topology F
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _) hF

/-- A property of the atlas that is stable under isomorphisms passes from `q : h_U ⟶ F` to its
extension `h_{j U} ≅ Λ h_U ⟶ Λ F`. -/
private theorem presheaf_relocalize_atlas (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    {F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B (B.inclusion.obj S) S.property} {q : yoneda.obj U ⟶ F}
    (hq : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (B.inclusion.obj S) S.property)).presheaf q) :
    (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (B.inclusion.obj S') S'.property)).presheaf
        (((relocalizeYonedaIso g).app U).inv ≫ (relocalizePresheafFunctor g).map q) :=
  MorphismProperty.RespectsIso.precomp _ _ _
    (@presheaf_map_relocalize _ _ _ _ g _ _
      (MorphismProperty.RespectsIso.inverseImage _ _) (fun _ hk => hk) _ _ _ hq)

/-- **Stacks 03I4, part (3), at the presheaf level.**  The relocalization of an algebraic space
over `S` along `g : S ⟶ S'` is an algebraic space over `S'`.

The three conditions are checked separately.  The relocalization of a sheaf is a sheaf
(`AlgebraicGeometry.Space.isSheaf_relocalize`).  The diagonal is representable because every
morphism from a representable presheaf into `Λ F` is `Λ` of a morphism from a representable
presheaf (`CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`), which is
representable by the representability of the diagonal of `F`, and because `Λ` carries
representable morphisms to representable morphisms
(`CategoryTheory.OverShriek.presheaf_map_relocalize`).  The atlas is the image under `Λ` of the
atlas of `F`, read through the comparison `Λ h_U ≅ h_{j U}`; it is surjective and étale by the
same transport, since `j = Over.map g` does not change the underlying morphism of schemes. -/
theorem isAlgebraicSpace_relocalize (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (B.inclusion.obj S) S.property F) :
    IsAlgebraicSpace B (B.inclusion.obj S') S'.property
      ((relocalizePresheafFunctor g).obj F) := by
  classical
  refine ⟨isSheaf_relocalize B S S' g F hF.isSheaf, ?_, ?_⟩
  · have _ : HasBinaryProducts (BigFppfOver B (B.inclusion.obj S) S.property) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    have _ : HasBinaryProducts (BigFppfOver B (B.inclusion.obj S') S'.property) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro W e
    obtain ⟨ψ, h, σ, hσ⟩ := exists_eq_relocalizeYonedaFactorIso_comp g e
    have hrepσ : yoneda.relativelyRepresentable σ :=
      Functor.relativelyRepresentable.of_diag hF.diagonal_representable σ
    have hpre : (MorphismProperty.inverseImage (⊤ : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (B.inclusion.obj S) S.property)).presheaf σ :=
      ⟨hrepσ, fun _ _ _ _ _ _ => trivial⟩
    have hext := presheaf_map_relocalize g
      (P₁ := MorphismProperty.inverseImage (⊤ : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (B.inclusion.obj S) S.property))
      (P₂ := MorphismProperty.inverseImage (⊤ : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (B.inclusion.obj S') S'.property))
      (fun _ _ => trivial) hpre
    rw [hσ]
    exact MorphismProperty.RespectsIso.precomp yoneda.relativelyRepresentable _ _ hext.1
  · have _ : MorphismProperty.RespectsIso
        (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    obtain ⟨U, q, hqSurj, hqEtale⟩ := hF.exists_atlas
    refine ⟨(Over.map g).obj U,
      ((relocalizeYonedaIso g).app U).inv ≫ (relocalizePresheafFunctor g).map q, ?_, ?_⟩
    · exact presheaf_relocalize_atlas B S S' g _ hqSurj
    · exact presheaf_relocalize_atlas B S S' g _ hqEtale

/-- **Stacks 03I4, part (3): the extended atlas has the extended kernel pair.**  If `R` is the
fibre product of an atlas `q : h_U ⟶ F` with itself over `S`, then `j R` is the fibre product
with itself of the extended atlas `h_{j U} ⟶ Λ F` over `S'`, along the images under
`j = Over.map g` of the two projections.  In particular those projections have the same
underlying morphisms of schemes as the original ones, so a property of them is inherited.

`Λ` preserves fibre products, `WalkingCospan` being connected
(`CategoryTheory.OverShriek.preservesLimitsOfShape_relocalizePresheafFunctor`), and the
comparison `Λ h_Z ≅ h_{j Z}` is natural in `Z`. -/
theorem isPullback_relocalize_atlas (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u}
    {U R : BigFppfOver B (B.inclusion.obj S) S.property} {q : yoneda.obj U ⟶ F}
    {r₁ r₂ : R ⟶ U} (h : IsPullback (yoneda.map r₁) (yoneda.map r₂) q q) :
    IsPullback (yoneda.map ((Over.map g).map r₁)) (yoneda.map ((Over.map g).map r₂))
      (((relocalizeYonedaIso g).app U).inv ≫ (relocalizePresheafFunctor g).map q)
      (((relocalizeYonedaIso g).app U).inv ≫ (relocalizePresheafFunctor g).map q) :=
  (h.map (relocalizePresheafFunctor g)).of_iso ((relocalizeYonedaIso g).app R)
    ((relocalizeYonedaIso g).app U) ((relocalizeYonedaIso g).app U) (Iso.refl _)
    ((relocalizeYonedaIso g).hom.naturality r₁) ((relocalizeYonedaIso g).hom.naturality r₂)
    (by simp) (by simp)

section Extend

variable (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
  {L : Sheaf (B.topology.over S) (Type u) ⥤ Sheaf (B.topology.over S') (Type u)}
  (adj : L ⊣ (Over.map g).sheafPushforwardContinuous (Type u)
    (B.topology.over S) (B.topology.over S'))

/-- The unit of `adj` at `X`, read as a morphism of presheaves `X ⟶ j^{-1}(L X)`. -/
private def extendUnit (X : Sheaf (B.topology.over S) (Type u)) :
    X.obj ⟶ (relocalizeRestrict g).obj ((L.obj X).obj) :=
  (adj.unit.app X).hom

/-- The identification `Λ X ≅ L X` of the presheaf-level relocalization with the extension,
`AlgebraicGeometry.isIso_relocalizeOfRestricted` read as an isomorphism. -/
private noncomputable def extendCompare (X : Sheaf (B.topology.over S) (Type u)) :
    (relocalizePresheafFunctor g).obj X.obj ≅ (L.obj X).obj :=
  @asIso _ _ _ _ (relocalizeOfRestricted g (extendUnit B S S' g adj X))
    (_root_.AlgebraicGeometry.isIso_relocalizeOfRestricted B S S' g adj X)

private theorem extendCompare_hom (X : Sheaf (B.topology.over S) (Type u)) :
    (extendCompare B S S' g adj X).hom =
      relocalizeOfRestricted g (extendUnit B S S' g adj X) :=
  rfl

private theorem extendUnit_naturality {X Y : Sheaf (B.topology.over S) (Type u)} (φ : X ⟶ Y) :
    φ.hom ≫ extendUnit B S S' g adj Y =
      extendUnit B S S' g adj X ≫ (relocalizeRestrict g).map ((L.map φ).hom) :=
  congrArg (fun k => k.hom) (adj.unit.naturality φ)

/-- `Λ X ≅ L X` is natural in `X`: both sides are the transpose under `Λ ⊣ j^{-1}` of the two
sides of the naturality of the unit of `adj`. -/
private theorem extendCompare_naturality {X Y : Sheaf (B.topology.over S) (Type u)} (φ : X ⟶ Y) :
    (relocalizePresheafFunctor g).map φ.hom ≫ (extendCompare B S S' g adj Y).hom =
      (extendCompare B S S' g adj X).hom ≫ (L.map φ).hom := by
  rw [extendCompare_hom, extendCompare_hom, map_comp_relocalizeOfRestricted,
    relocalizeOfRestricted_comp, extendUnit_naturality]

private theorem extendCompare_inv_naturality {X Y : Sheaf (B.topology.over S) (Type u)}
    (φ : X ⟶ Y) :
    (extendCompare B S S' g adj X).inv ≫ (relocalizePresheafFunctor g).map φ.hom =
      (L.map φ).hom ≫ (extendCompare B S S' g adj Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact extendCompare_naturality B S S' g adj φ

end Extend

/-- **Stacks 03I4, part (3): the extension of a presentation.** A chosen étale presentation `U / R`
of an algebraic space `F` over `S` extends along `g : S ⟶ S'` to a presentation of `L F` by the
images `j U` and `j R` of `U` and `R`, where `j = Over.map g`.

The data produced is the identification `α : L h_U ≅ h_{j U}` of the extension of the representable
`h_U`, and the extended atlas `f : h_{j U} ⟶ L F`, which is `L` of the original atlas read through
`α`.  Its kernel pair is the pair of images `j` of the two projections of `R`; those two make `j R`
an étale equivalence relation on `j U` over `S'`; `f` is surjective and étale after every
representable base change; and `f` exhibits `L F` as the coequalizer of its kernel pair in sheaves
over `S'`.

The quotient is specified by this universal property rather than by a sheafification, so that no
smallness hypothesis on sheafification is needed on either slice. -/
@[stacks 03I4 "extension_algebraic_space"]
theorem exists_extended_presentation
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤ Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous (Type u)
      (B.topology.over S) (B.topology.over S'))
    (F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (B.inclusion.obj S) S.property F)
    (P : Presentation B (B.inclusion.obj S) S.property F hF) :
    let J := B.topology.over S
    let J' := BigFppfOver.topology B (B.inclusion.obj S') S'.property
    let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
    let G := (L.obj FF).obj
    let target := (Over.map g).map P.target
    let source := (Over.map g).map P.source
    ∃ (hU : Presheaf.IsSheaf J (yoneda.obj P.U))
      (hU' : Presheaf.IsSheaf J' (yoneda.obj ((Over.map g).obj P.U)))
      (hR' : Presheaf.IsSheaf J' (yoneda.obj ((Over.map g).obj P.R)))
      (α : (L.obj (⟨yoneda.obj P.U, hU⟩ : Sheaf J (Type u))).obj ≅
        yoneda.obj ((Over.map g).obj P.U))
      (f : yoneda.obj ((Over.map g).obj P.U) ⟶ G)
      (hpb : IsPullback (yoneda.map target) (yoneda.map source) f f),
      let UF : Sheaf J' (Type u) := ⟨yoneda.obj ((Over.map g).obj P.U), hU'⟩
      let RF : Sheaf J' (Type u) := ⟨yoneda.obj ((Over.map g).obj P.R), hR'⟩
      let tf : RF ⟶ UF := ⟨yoneda.map target⟩
      let sf : RF ⟶ UF := ⟨yoneda.map source⟩
      let ff : UF ⟶ L.obj FF := ⟨f⟩
      let w : tf ≫ ff = sf ≫ ff := Sheaf.hom_ext hpb.w
      Stacks.Groupoids.IsEtaleEquivalenceRelation
        (prod.lift ((Over.post B.inclusion).map target)
          ((Over.post B.inclusion).map source)) ∧
      f = α.inv ≫ (L.map (⟨P.toSpace⟩ :
        (⟨yoneda.obj P.U, hU⟩ : Sheaf J (Type u)) ⟶ FF)).hom ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (B.inclusion.obj S') S'.property))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (B.inclusion.obj S') S'.property))) f ∧
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  classical
  dsimp only
  have _ : MorphismProperty.RespectsIso (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hU : Presheaf.IsSheaf (B.topology.over S) (yoneda.obj P.U) :=
    BigFppfOver.isSheaf_yoneda_obj B (B.inclusion.obj S) S.property P.U
  have hU' : Presheaf.IsSheaf (BigFppfOver.topology B (B.inclusion.obj S') S'.property)
      (yoneda.obj ((Over.map g).obj P.U)) :=
    BigFppfOver.isSheaf_yoneda_obj B (B.inclusion.obj S') S'.property ((Over.map g).obj P.U)
  have hR' : Presheaf.IsSheaf (BigFppfOver.topology B (B.inclusion.obj S') S'.property)
      (yoneda.obj ((Over.map g).obj P.R)) :=
    BigFppfOver.isSheaf_yoneda_obj B (B.inclusion.obj S') S'.property ((Over.map g).obj P.R)
  let FF : Sheaf (B.topology.over S) (Type u) := ⟨F, hF.isSheaf⟩
  let U₀ : Sheaf (B.topology.over S) (Type u) := ⟨yoneda.obj P.U, hU⟩
  let q₀ : U₀ ⟶ FF := ⟨P.toSpace⟩
  let α : (L.obj U₀).obj ≅ yoneda.obj ((Over.map g).obj P.U) :=
    (extendCompare B S S' g adj U₀).symm ≪≫ (relocalizeYonedaIso g).app P.U
  let A : yoneda.obj ((Over.map g).obj P.U) ⟶ (relocalizePresheafFunctor g).obj F :=
    ((relocalizeYonedaIso g).app P.U).inv ≫ (relocalizePresheafFunctor g).map P.toSpace
  have hnat : (relocalizePresheafFunctor g).map P.toSpace ≫
      (extendCompare B S S' g adj FF).hom =
      (extendCompare B S S' g adj U₀).hom ≫ (L.map q₀).hom :=
    extendCompare_naturality B S S' g adj q₀
  have hf : A ≫ (extendCompare B S S' g adj FF).hom = α.inv ≫ (L.map q₀).hom := by
    change (((relocalizeYonedaIso g).app P.U).inv ≫
        (relocalizePresheafFunctor g).map P.toSpace) ≫ (extendCompare B S S' g adj FF).hom =
      ((extendCompare B S S' g adj U₀).symm ≪≫
        (relocalizeYonedaIso g).app P.U).inv ≫ (L.map q₀).hom
    rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, Category.assoc, hnat]
  have hpbA : IsPullback (yoneda.map ((Over.map g).map P.target))
      (yoneda.map ((Over.map g).map P.source)) A A :=
    isPullback_relocalize_atlas B S S' g P.isPullback
  have hpb : IsPullback (yoneda.map ((Over.map g).map P.target))
      (yoneda.map ((Over.map g).map P.source))
      (A ≫ (extendCompare B S S' g adj FF).hom)
      (A ≫ (extendCompare B S S' g adj FF).hom) :=
    hpbA.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (extendCompare B S S' g adj FF)
      (by simp) (by simp) (by simp) (by simp)
  have hArel : ∀ Q : MorphismProperty Scheme.{u}, Q.RespectsIso →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
        (BigFppfOver.toScheme B (B.inclusion.obj S) S.property))) P.toSpace →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
        (BigFppfOver.toScheme B (B.inclusion.obj S') S'.property)))
        (A ≫ (extendCompare B S S' g adj FF).hom) := by
    intro Q hQ hP
    exact MorphismProperty.RespectsIso.postcomp _ _ _ (presheaf_relocalize_atlas B S S' g Q hP)
  refine ⟨hU, hU', hR', α, A ≫ (extendCompare B S S' g adj FF).hom, hpb, ?_, hf,
    hArel _ inferInstance P.surjective, hArel _ inferInstance P.etale, ?_⟩
  · have hEq : IsEquivalenceRelation
        ((Over.post B.inclusion).map ((Over.map g).map P.target))
        ((Over.post B.inclusion).map ((Over.map g).map P.source)) :=
      isEquivalenceRelation_of_isPullback B (B.inclusion.obj S') S'.property
        (A ≫ (extendCompare B S S' g adj FF).hom) ((Over.map g).map P.target)
        ((Over.map g).map P.source) hpb
    have hEs : Etale ((Over.post B.inclusion).map P.source).left := by
      simpa only [Stacks.Groupoids.PreRelation.source, prod.lift_snd] using
        P.isEtaleEquivalenceRelation.etale_source
    have hEt : Etale ((Over.post B.inclusion).map P.target).left := by
      simpa only [Stacks.Groupoids.PreRelation.target, prod.lift_fst] using
        P.isEtaleEquivalenceRelation.etale_target
    refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
    · simpa only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
        prod.lift_fst, prod.lift_snd] using hEq
    · simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
      exact hEs
    · simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
      exact hEt
  · have hR : Presheaf.IsSheaf (B.topology.over S) (yoneda.obj P.R) :=
      BigFppfOver.isSheaf_yoneda_obj B (B.inclusion.obj S) S.property P.R
    let R₀ : Sheaf (B.topology.over S) (Type u) := ⟨yoneda.obj P.R, hR⟩
    let tf₀ : R₀ ⟶ U₀ := ⟨yoneda.map P.target⟩
    let sf₀ : R₀ ⟶ U₀ := ⟨yoneda.map P.source⟩
    have w₀ : tf₀ ≫ q₀ = sf₀ ≫ q₀ := Sheaf.hom_ext P.isPullback.w
    have hc₀' : Nonempty (IsColimit (Cofork.ofπ q₀ w₀)) := by
      obtain ⟨hRsh, hUsh, hcoe⟩ := isCoequalizer_of_surjectiveEtale B (B.inclusion.obj S)
        S.property P.toSpace P.target P.source P.isPullback hF P.surjective P.etale
      exact hcoe
    have hc₀ := Classical.choice hc₀'
    have _ : PreservesColimitsOfShape WalkingParallelPair L :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    have hcL : IsColimit (Cofork.ofπ (L.map q₀)
        (show L.map tf₀ ≫ L.map q₀ = L.map sf₀ ≫ L.map q₀ by
          simp only [← L.map_comp, w₀]) : Cofork (L.map tf₀) (L.map sf₀)) :=
      isColimitCoforkMapOfIsColimit L w₀ hc₀
    let αR : (L.obj R₀).obj ≅ yoneda.obj ((Over.map g).obj P.R) :=
      (extendCompare B S S' g adj R₀).symm ≪≫ (relocalizeYonedaIso g).app P.R
    let βU : L.obj U₀ ≅ ⟨yoneda.obj ((Over.map g).obj P.U), hU'⟩ := ObjectProperty.isoMk _ α
    let βR : L.obj R₀ ≅ ⟨yoneda.obj ((Over.map g).obj P.R), hR'⟩ := ObjectProperty.isoMk _ αR
    have hcomm : ∀ (r : P.R ⟶ P.U) (rf : R₀ ⟶ U₀), rf.hom = yoneda.map r →
        βR.hom ≫ (⟨yoneda.map ((Over.map g).map r)⟩ :
          (⟨yoneda.obj ((Over.map g).obj P.R), hR'⟩ : Sheaf _ (Type u)) ⟶
            ⟨yoneda.obj ((Over.map g).obj P.U), hU'⟩) = L.map rf ≫ βU.hom := by
      intro r rf hrf
      have hρ : (relocalizePresheafFunctor g).map (yoneda.map r) ≫
          ((relocalizeYonedaIso g).app P.U).hom =
          ((relocalizeYonedaIso g).app P.R).hom ≫ yoneda.map ((Over.map g).map r) :=
        (relocalizeYonedaIso g).hom.naturality r
      refine Sheaf.hom_ext ?_
      change ((extendCompare B S S' g adj R₀).symm ≪≫ (relocalizeYonedaIso g).app P.R).hom ≫
          yoneda.map ((Over.map g).map r) =
        (L.map rf).hom ≫ ((extendCompare B S S' g adj U₀).symm ≪≫
          (relocalizeYonedaIso g).app P.U).hom
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc, ← hρ,
        ← Category.assoc, ← Category.assoc, ← hrf,
        extendCompare_inv_naturality B S S' g adj rf]
    refine ⟨Cofork.isColimitOfIsos _ hcL _ βR βU (Iso.refl _) (hcomm P.target tf₀ rfl)
      (hcomm P.source sf₀ rfl) ?_⟩
    refine Sheaf.hom_ext ?_
    change α.inv ≫ (L.map q₀).hom ≫ 𝟙 _ = A ≫ (extendCompare B S S' g adj FF).hom
    rw [Category.comp_id]
    exact hf.symm

end Space

end AlgebraicGeometry

/-! ### Evaluation of a restricted sheaf

Restriction along the relocalization functor `CategoryTheory.Over.map g` is its inverse
image operation on sheaves, so a restricted sheaf is evaluated at `T / S` by evaluating the
original sheaf at the composite `T / S'`. That is Mathlib's general evaluation formula for
restriction along a continuous functor; its instance for the big fppf site is
`AlgebraicGeometry.Space.restrict_eval` above. -/

add_to_stacks 03I4 "restriction_evaluation"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj

end
