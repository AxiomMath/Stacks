module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGerms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareLiftCounts

/-!
# Glueing submodules across an elementary distinguished square

Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square of algebraic spaces (Stacks 08GM)
and `ℱ` an `𝒪_W`-module.  Given submodules `𝒢 ⊆ ℱ|_U` and `𝒩 ⊆ ℱ|_V` which agree over
`U ×_W V` — in the chartwise sense that restriction along a morphism of charts of `W` between a
chart of `U` and a chart of `V`, in either direction, carries one into the other — this file
produces a submodule of `ℱ` restricting to `𝒢` on `U` and to `𝒩` on `V`.

The content is that no further compatibility is needed: a submodule of `ℱ|_V` is in general not
the restriction of a submodule of `ℱ`, because the two pullbacks of it to `V ×_W V` need not
agree, and the square guarantees that they do.  This is checked at the geometric points of `W`,
through the germ sets of `StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGerms`: a geometric
point outside `U` has exactly one lift to `V` (Stacks 08GM, the étale morphism is an isomorphism
over the reduced complement of `U`), and at a geometric point of `U` the germ set of `𝒩` at any
lift is the germ set of `𝒢`, both being the germ set of the common restriction to `U ×_W V`.

## Main results

* `AlgebraicGeometry.Space.etaleGermSet_congr`: germ sets along equal étale morphisms agree as
  soon as the submodules do chartwise.
* `AlgebraicGeometry.Space.etaleGermSet_edsEtaleHom_subset`: the germ set of `𝒩` at a geometric
  point of `W` does not depend on the lift to `V`.
* `AlgebraicGeometry.Space.exists_etaleSubmodule_eds_glue`: the glueing.

## References

* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Germ sets along equal étale morphisms.**  For two equal étale morphisms `a = b : Y ⟶ X`,
submodules `Nₐ ⊆ M|_Y` (along `a`) and `N_b ⊆ M|_Y` (along `b`) carried into one another by
restriction along every morphism of charts of `X` between `a ∘ V` and `b ∘ V` have the same germ
sets at lifts with the same underlying section. -/
theorem etaleGermSet_congr {X Y : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}
    {a b : Y ⟶ X} (hab : a = b) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (Na : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule)
    (Nb : ((etaleModulePullback.{u, u} B S hS b hb).obj M).Submodule)
    (h₁ : ∀ (V : SmallEtale B S hS Y.1)
      (φ : (smallEtalePostcomp B S hS a ha).obj V ⟶ (smallEtalePostcomp B S hS b hb).obj V)
      (n : M.val.obj (op ((smallEtalePostcomp B S hS b hb).obj V))),
      n ∈ Nb.obj (op V) → M.val.map φ.op n ∈ Na.obj (op V))
    (h₂ : ∀ (V : SmallEtale B S hS Y.1)
      (φ : (smallEtalePostcomp B S hS b hb).obj V ⟶ (smallEtalePostcomp B S hS a ha).obj V)
      (n : M.val.obj (op ((smallEtalePostcomp B S hS a ha).obj V))),
      n ∈ Na.obj (op V) → M.val.map φ.op n ∈ Nb.obj (op V))
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS a.hom x)
    (t' : GeometricPointLift B S hS b.hom x) (htt : t.1 = t'.1) :
    etaleGermSet B S hS a ha Na t = etaleGermSet B S hS b hb Nb t' := by
  subst hab
  obtain rfl : t = t' := Subtype.ext htt
  refine Set.eq_of_subset_of_subset ?_ ?_ <;> rintro e ⟨V, w, n, hn, rfl⟩ <;>
    refine ⟨V, w, n, ?_, rfl⟩
  · have := h₂ V (𝟙 _) n hn
    rwa [op_id, moduleMap_id_apply'] at this
  · have := h₁ V (𝟙 _) n hn
    rwa [op_id, moduleMap_id_apply'] at this

/-- The open subspace `U` of an algebraic space `W`, as an algebraic space with its inclusion. -/
def openSubspaceSpace {W : AlgebraicSpaces B S hS} (U : Subfunctor W.1)
    (hU : IsOpenSubspace B S hS U) : AlgebraicSpaces B S hS :=
  ⟨U.toFunctor, hU.1⟩

/-- The inclusion of an open subspace, as a morphism of algebraic spaces. -/
def openSubspaceHom {W : AlgebraicSpaces B S hS} (U : Subfunctor W.1)
    (hU : IsOpenSubspace B S hS U) : openSubspaceSpace B S hS U hU ⟶ W :=
  ObjectProperty.homMk U.ι

/-- The inclusion of an open subspace is étale. -/
theorem isEtale_openSubspaceHom {W : AlgebraicSpaces B S hS} (U : Subfunctor W.1)
    (hU : IsOpenSubspace B S hS U) : IsEtale B S hS (openSubspaceHom B S hS U hU).hom :=
  isEtale_of_isOpenImmersion B S hS hU.2

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  (U : Subfunctor W.1) (hU : IsOpenSubspace B S hS U) (hUoU : Uo ≤ U)
  {F : Modules.{u, u} B S hS W.1 W.2}
  {G : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U hU)
    (isEtale_openSubspaceHom B S hS U hU)).obj F).Submodule}
  {NV : ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).obj F).Submodule}

/-- The germ-set form of the agreement of `𝒢` and `𝒩` over `U ×_W V`: at every geometric point
of `W` lifting to both, the two germ sets agree. -/
def EdsGermAgree (G : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U hU)
    (isEtale_openSubspaceHom B S hS U hU)).obj F).Submodule)
    (NV : ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj F).Submodule) : Prop :=
  ∀ (x : GeometricPoint B S hS W.1)
    (t : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x)
    (u : GeometricPointLift B S hS (openSubspaceHom B S hS U hU).hom x),
    etaleGermSet B S hS _ (isEtale_edsEtaleHom B S hS hsq) NV t =
      etaleGermSet B S hS _ (isEtale_openSubspaceHom B S hS U hU) G u

include hUoU in
/-- **The germ set of `𝒩` does not depend on the lift.**  Outside `U` the lift to `V` is unique,
the point lying outside `Uo` (Stacks 08GM); inside, every germ set of `𝒩` is the germ set of
`𝒢`. -/
theorem etaleGermSet_edsEtaleHom_subset (h : EdsGermAgree B S hS hsq U hU G NV)
    {x : GeometricPoint B S hS W.1}
    (t₁ t₂ : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) :
    etaleGermSet B S hS _ (isEtale_edsEtaleHom B S hS hsq) NV t₂ ⊆
      etaleGermSet B S hS _ (isEtale_edsEtaleHom B S hS hsq) NV t₁ := by
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · obtain ⟨u⟩ := (nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 U hU x).2 hx
    rw [h x t₁ u, h x t₂ u]
  · have hxo : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := fun hmem => hx <| by
      obtain ⟨u⟩ := (nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 Uo
        hsq.isOpenSubspace x).2 hmem
      exact (nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 U hU x).1
        ⟨⟨u.1.1, hUoU _ u.1.2⟩, u.2⟩
    have : Subsingleton (GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) :=
      subsingleton_geometricPointLift_of_notMem_range_pointsMap B S hS W.2 Uo fV hsq x hxo
    rw [Subsingleton.elim t₂ t₁]

/-- The two members: the open subspace `U` at `true` and the étale algebraic space at `false`. -/
def edsMember : ULift.{u} Bool → AlgebraicSpaces B S hS
  | ⟨true⟩ => openSubspaceSpace B S hS U hU
  | ⟨false⟩ => edsEtale B S hS hsq

/-- The morphisms from the two members to the ambient space. -/
def edsMemberHom : ∀ b, edsMember B S hS hsq U hU b ⟶ W
  | ⟨true⟩ => openSubspaceHom B S hS U hU
  | ⟨false⟩ => edsEtaleHom B S hS hsq

/-- The morphisms from the two members to the ambient space are étale. -/
theorem isEtale_edsMemberHom : ∀ b, IsEtale B S hS (edsMemberHom B S hS hsq U hU b).hom
  | ⟨true⟩ => isEtale_openSubspaceHom B S hS U hU
  | ⟨false⟩ => isEtale_edsEtaleHom B S hS hsq

variable (G NV) in
/-- The submodules over the two members. -/
def edsMemberSubmodule : ∀ b, ((etaleModulePullback.{u, u} B S hS (edsMemberHom B S hS hsq U hU b)
    (isEtale_edsMemberHom B S hS hsq U hU b)).obj F).Submodule
  | ⟨true⟩ => G
  | ⟨false⟩ => NV

include hUoU in
/-- **The two submodules form a compatible family.** -/
theorem edsMemberSubmodule_compatible (h : EdsGermAgree B S hS hsq U hU G NV) :
    EtaleSubmoduleFamily.Compatible B S hS (edsMember B S hS hsq U hU)
      (edsMemberHom B S hS hsq U hU) (isEtale_edsMemberHom B S hS hsq U hU)
      (edsMemberSubmodule B S hS hsq U hU G NV) := by
  rintro ⟨_ | _⟩ ⟨_ | _⟩ V V' φ n hn
  · exact map_mem_of_etaleGermSet_subset B S hS _ (isEtale_edsEtaleHom B S hS hsq) _
      (isEtale_edsEtaleHom B S hS hsq) NV NV
      (fun x t t' => etaleGermSet_edsEtaleHom_subset B S hS hsq U hU hUoU h t t') V V' φ n hn
  · exact map_mem_of_etaleGermSet_subset B S hS _ (isEtale_edsEtaleHom B S hS hsq) _
      (isEtale_openSubspaceHom B S hS U hU) NV G
      (fun x t t' => (h x t t').ge) V V' φ n hn
  · exact map_mem_of_etaleGermSet_subset B S hS _ (isEtale_openSubspaceHom B S hS U hU) _
      (isEtale_edsEtaleHom B S hS hsq) G NV
      (fun x t t' => (h x t' t).le) V V' φ n hn
  · refine map_mem_of_etaleGermSet_subset B S hS _ (isEtale_openSubspaceHom B S hS U hU) _
      (isEtale_openSubspaceHom B S hS U hU) G G (fun x t t' => ?_) V V' φ n hn
    have : Subsingleton (GeometricPointLift B S hS (openSubspaceHom B S hS U hU).hom x) :=
      subsingleton_geometricPointLift_of_mono B S hS U.ι inferInstance x
    rw [Subsingleton.elim t' t]

include hUoU in
/-- **Glueing submodules across an elementary distinguished square.**  Let `(Uo ⊆ W, f : V ⟶ W)`
be an elementary distinguished square and `U ⊇ Uo` an open subspace.  Submodules `𝒢 ⊆ ℱ|_U` and
`𝒩 ⊆ ℱ|_V` whose germ sets agree at every geometric point lifting to both are the restrictions
of one submodule of `ℱ`. -/
theorem exists_etaleSubmodule_eds_glue (h : EdsGermAgree B S hS hsq U hU G NV) :
    ∃ N : F.Submodule,
      etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U hU) N = G ∧
        etaleSubmoduleRestrict B S hS _ (isEtale_edsEtaleHom B S hS hsq) N = NV :=
  ⟨etaleSubmoduleGlue B S hS _ _ _ (edsMemberSubmodule B S hS hsq U hU G NV),
    etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _
      (edsMemberSubmodule_compatible B S hS hsq U hU hUoU h) ⟨true⟩,
    etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _
      (edsMemberSubmodule_compatible B S hS hsq U hU hUoU h) ⟨false⟩⟩

end Square

end AlgebraicGeometry.Space

end
