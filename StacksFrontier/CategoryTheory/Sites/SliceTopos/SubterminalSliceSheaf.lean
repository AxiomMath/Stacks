module

public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSliceEquiv
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSliceRestrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The slice of a topos at a subterminal sheaf

Let `F` be a sheaf of sets with subsingleton values on a site `(C, J)` and let `j : D ⥤ C` be a
fully faithful continuous functor whose essential image is the support of `F` and whose covering
sieves are exactly the sieves whose image covers.  Then restriction along `j` is an equivalence
`Sh(C)/F ≌ Sh(D)`.

This is [Stacks, Tag 0791] for a subterminal `F`, and unlike the general statement
`CategoryTheory.Stacks.Topos.Localized.sheafEquivalence` it holds for sheaves of sets in an
arbitrary universe `w`, with no relation to the universe of the morphisms of `C`.  That is what
it is for: the crystalline and small Zariski topoi of [Stacks, Tag 07KL] have objects in
`Type (u + 1)` and morphisms in `Type u`, and take values in `Type (u + 1)`, so the general 0791
— whose site of elements `CostructuredArrow yoneda F` does not even typecheck there, and whose
proof rests on Mathlib's `OverPresheafAux` — does not apply.

The content beyond the presheaf layer of `SubterminalSlice.lean` is that the extension by the
empty set of a sheaf on `D` is a sheaf on `C`.  Over an object outside the support of `F` the
extension is empty, and no covering sieve of such an object can carry a family of elements,
because `F` is itself a sheaf with subsingleton values; over an object inside the support the
extension is, after transport to the chosen object of `D` above it, the original sheaf, and the
covering sieves correspond.

## Main results

* `CategoryTheory.Stacks.Topos.Subterminal.isSheaf_extend` — extension by the empty set
  preserves sheaves.
* `CategoryTheory.Stacks.Topos.Subterminal.essSurj_sliceRestriction` — every sheaf on `D` is a
  restriction.
* `CategoryTheory.Stacks.Topos.Subterminal.sliceEquivalence` — the equivalence
  `Sh(D) ≌ Sh(C)/F`.

## References

* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Stacks.Topos.Subterminal

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : Cᵒᵖ ⥤ Type w} {j : D ⥤ C} [j.Full] [j.Faithful]
  [∀ X : Cᵒᵖ, Subsingleton (F.obj X)]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (hsupp : ∀ U : C, Nonempty (F.obj (op U)) → j.essImage U)
  (hmem : ∀ B : D, Nonempty (F.obj (op (j.obj B))))

include hsupp hmem in
/-- The restriction isomorphism is natural, read as a transport of sections. -/
theorem restrictExtendIso_hom_naturality (H : Dᵒᵖ ⥤ Type w) {B B' : D} (k : B' ⟶ B)
    (p : (extend F j hsupp H).obj (op (j.obj B))) :
    (restrictExtendIso hsupp hmem H).hom.app (op B')
        ((extend F j hsupp H).map (j.map k).op p) =
      H.map k.op ((restrictExtendIso hsupp hmem H).hom.app (op B) p) :=
  NatTrans.naturality_apply (restrictExtendIso hsupp hmem H).hom k.op p

include hsupp hmem in
/-- Transporting a section of the extension over `j B` back to `B` along the morphism of `D`
underlying a morphism of `C` out of `j B` undoes the restriction of the extension. -/
theorem restrictExtendIso_hom_app_map (H : Dᵒᵖ ⥤ Type w) {V : C} {B : D} (a : j.obj B ⟶ V)
    (q : (extend F j hsupp H).obj (op V)) :
    (restrictExtendIso hsupp hmem H).hom.app (op B) ((extend F j hsupp H).map a.op q) = by
      exact H.map (srcIsoSelf hsupp B (F.map a.op q.1)).inv.op
        (H.map (srcHom hsupp a.op q.1).op q.2) :=
  rfl

include hsupp hmem in
/-- **The extension by the empty set of a sheaf is a sheaf.**  Over an object outside the
support of `F` the extension is empty, and no covering sieve of such an object can carry a
family of elements, `F` itself being a sheaf with subsingleton values.  Over an object inside
the support the extension is, after transport to the chosen object `A` of `D` above it, the
sheaf `H`, and the covering sieves of `A` are exactly the pullbacks of those below. -/
theorem isSheaf_extend (hF : Presheaf.IsSheaf J F)
    (hcover : ∀ (A : D) (T : Sieve A), T ∈ K A ↔ T.functorPushforward j ∈ J (j.obj A))
    {H : Dᵒᵖ ⥤ Type w} (hH : Presheaf.IsSheaf K H) :
    Presheaf.IsSheaf J (extend F j hsupp H) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  by_cases hU : Nonempty (F.obj (op U))
  swap
  · exact absurd ((Presheaf.isSheaf_iff_nonempty_of_subsingleton J F).mp hF U S hS
      fun V f hf ↦ ⟨(x f hf).1⟩) hU
  obtain ⟨s₀⟩ := hU
  have harr : ∀ {B : D} (g : B ⟶ srcObj hsupp s₀),
      ((S.pullback (srcIso hsupp s₀).hom).functorPullback j).arrows g →
        S.arrows (j.map g ≫ (srcIso hsupp s₀).hom) := fun _ hg ↦ hg
  have hTK : (S.pullback (srcIso hsupp s₀).hom).functorPullback j ∈ K (srcObj hsupp s₀) := by
    rw [hcover, functorPushforward_functorPullback_of_essImage hmem hsupp]
    exact J.pullback_stable _ hS
  obtain ⟨t, ht, htu⟩ := (isSheaf_iff_isSheaf_of_type K H).mp hH _ hTK
    (fun B g hg ↦ (restrictExtendIso hsupp hmem H).hom.app (op B)
      (x (j.map g ≫ (srcIso hsupp s₀).hom) (harr g hg)))
    (by
      intro B₁ B₂ Z k₁ k₂ g₁ g₂ h₁ h₂ hk
      rw [← restrictExtendIso_hom_naturality, ← restrictExtendIso_hom_naturality]
      congr 1
      exact hx (j.map k₁) (j.map k₂) (harr g₁ h₁) (harr g₂ h₂)
        (by rw [← Category.assoc, ← j.map_comp, hk, j.map_comp, Category.assoc]))
  refine ⟨⟨s₀, t⟩, ?_, ?_⟩
  · intro V f hf
    have hgT : ((S.pullback (srcIso hsupp s₀).hom).functorPullback j).arrows
        (srcHom hsupp f.op s₀) := by
      show S.arrows (j.map (srcHom hsupp f.op s₀) ≫ (srcIso hsupp s₀).hom)
      rw [map_srcHom]
      simpa using S.downward_closed hf (srcIso hsupp (F.map f.op s₀)).hom
    refine extend_ext hsupp ?_
    have hx2 : x (j.map (srcHom hsupp f.op s₀) ≫ (srcIso hsupp s₀).hom) (harr _ hgT) =
        (extend F j hsupp H).map ((srcIso hsupp (F.map f.op s₀)).hom).op (x f hf) := by
      have hcom := hx ((srcIso hsupp (F.map f.op s₀)).hom) (𝟙 _) hf (harr _ hgT)
        (by rw [map_srcHom]; simp)
      simpa using hcom.symm
    refine (ht _ hgT).trans ?_
    simp only []
    rw [hx2, restrictExtendIso_hom_app_map]
    have hkey : srcHom hsupp ((srcIso hsupp (F.map f.op s₀)).hom).op (x f hf).1 =
        (srcIsoSelf hsupp (srcObj hsupp (F.map f.op s₀))
          (F.map ((srcIso hsupp (F.map f.op s₀)).hom).op (x f hf).1)).hom := by
      apply j.map_injective
      rw [map_srcHom, map_srcIsoSelf_hom]
      show (srcIso hsupp (F.map ((srcIso hsupp (F.map f.op s₀)).hom).op (x f hf).1)).hom ≫
          (srcIso hsupp (F.map f.op s₀)).hom ≫ (srcIso hsupp (F.map f.op s₀)).inv =
        (srcIso hsupp (F.map ((srcIso hsupp (F.map f.op s₀)).hom).op (x f hf).1)).hom
      simp
    rw [hkey, map_srcIsoSelf_inv_hom]
  · intro q hq
    refine extend_ext hsupp ?_
    refine htu q.2 fun {B} g hg ↦ ?_
    have hq' := hq (j.map g ≫ (srcIso hsupp s₀).hom) (harr g hg)
    simp only []
    rw [← hq', restrictExtendIso_hom_app_map]
    have hkey : (srcIsoSelf hsupp B (F.map (j.map g ≫ (srcIso hsupp s₀).hom).op q.1)).inv ≫
        srcHom hsupp (j.map g ≫ (srcIso hsupp s₀).hom).op q.1 = g := by
      apply j.map_injective
      rw [j.map_comp, map_srcHom, map_srcIsoSelf_inv]
      show (srcIso hsupp (F.map (j.map g ≫ (srcIso hsupp s₀).hom).op q.1)).inv ≫
          (srcIso hsupp (F.map (j.map g ≫ (srcIso hsupp s₀).hom).op q.1)).hom ≫
            (j.map g ≫ (srcIso hsupp s₀).hom) ≫ (srcIso hsupp s₀).inv = j.map g
      simp
    rw [← Functor.map_comp_apply, ← op_comp, hkey]

section Equivalence

variable [j.IsContinuous K J] (hF : Presheaf.IsSheaf J F)
  (hcover : ∀ (A : D) (T : Sieve A), T ∈ K A ↔ T.functorPushforward j ∈ J (j.obj A))

include hsupp hmem hcover in
/-- **Every sheaf on `D` is the restriction of one over `F`**, namely of its extension by the
empty set, whose structure map to `F` is the projection. -/
theorem essSurj_sliceRestriction : (sliceRestriction (j := j) (K := K) hF).EssSurj where
  mem_essImage H :=
    ⟨Over.mk (Y := (⟨extend F j hsupp H.obj,
        isSheaf_extend hsupp hmem hF hcover H.property⟩ : Sheaf J (Type w)))
      (ObjectProperty.homMk (extendπ F j hsupp H.obj)),
      ⟨ObjectProperty.isoMk _ (restrictExtendIso hsupp hmem H.obj)⟩⟩

include hsupp hmem hcover in
/-- **[Stacks, Tag 0791] for a subterminal sheaf, in an arbitrary coefficient universe.**  Let
`F` be a sheaf of sets on `(C, J)` with subsingleton values and let `j : D ⥤ C` be a fully
faithful continuous functor whose essential image is the support of `F` and whose covering
sieves are exactly those whose image covers.  Then `Sh(D) ≌ Sh(C)/F`.

Unlike `CategoryTheory.Stacks.Topos.Localized.sheafEquivalence`, this carries no constraint
between the coefficient universe `w` and the universe of the morphisms of `C`: the fibre
`{t ∈ P(U) | φ(t) = s}` of a map to a subterminal `F` is all of `P(U)`, so the fibre functor is
plain restriction and Mathlib's `OverPresheafAux`, which exists only at the hom universe, is not
needed. -/
@[sga "4 III 5.4" "special case", sga "4 VI 7.3.2" "special case"]
noncomputable def sliceEquivalence :
    Sheaf K (Type w) ≌ Over (⟨F, hF⟩ : Sheaf J (Type w)) :=
  haveI : (sliceRestriction (j := j) (K := K) hF).IsEquivalence :=
    ⟨faithful_sliceRestriction hsupp hF, full_sliceRestriction hsupp hF,
      essSurj_sliceRestriction hsupp hmem hF hcover⟩
  (sliceRestriction (j := j) (K := K) hF).asEquivalence.symm

include hsupp hmem hcover in
/-- The inverse of the slice equivalence is restriction along `j`. -/
theorem sliceEquivalence_inverse :
    (sliceEquivalence hsupp hmem hF hcover).inverse = sliceRestriction (j := j) (K := K) hF :=
  rfl

end Equivalence

end Stacks.Topos.Subterminal

end CategoryTheory

end
