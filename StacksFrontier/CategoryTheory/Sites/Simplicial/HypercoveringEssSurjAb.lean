module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringEssSurj
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# Every cartesian abelian sheaf on the total site of a hypercovering is an inverse image

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf. This file proves the two clauses of Stacks 0D8E (2) that concern the essential
image: a cartesian sheaf of abelian groups on the total site `(C/K)_total` lies in the essential
image of restriction along the localization functor `j_total`, so that essential image is exactly
the cartesian abelian sheaves and the counit `a⁻¹ a_* F ⟶ F` is invertible on them.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.ranSubgroupAb` and `.ranPresheafAb`: the right Kan
  extension along `j_total` of a sheaf of abelian groups on the total site, obtained by putting
  the pointwise group structure on the sections of the set-valued Kan extension
  `CategoryTheory.SimplicialSemiRepresentable.ranPresheaf`.
* `CategoryTheory.SimplicialSemiRepresentable.ranEvAb`: the comparison morphism from the
  restriction of that Kan extension back to the original abelian sheaf.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isSheaf_ranPresheafAb`: the abelian Kan extension
  of an abelian sheaf is a sheaf.
* `CategoryTheory.SimplicialSemiRepresentable.essImage_of_rigidAb`: a rigid sheaf of abelian
  groups on the total site is an inverse image along `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.essImage_of_isCartesianAbSheaf`: **Stacks 0D8E
  (2), essential surjectivity onto the cartesian abelian sheaves.**
* `CategoryTheory.SimplicialSemiRepresentable.mem_essImage_iff_isCartesianAbSheaf'` and
  `.isIso_abelianCounit_app_hypercovering'`: **Stacks 0D8E (2)**, the essential image of `a⁻¹` on
  abelian sheaves is exactly the cartesian ones, and the counit `a⁻¹ a_* F ⟶ F` is invertible on
  them.

## Implementation notes

Nothing is reproved here: the whole content is the set-valued statement of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringEssSurj.lean`, applied to the
underlying sheaf of sets `G ⋙ forget Ab` — which is exactly what
`CategoryTheory.SimplicialSiteSituation.IsCartesianAbSheaf` is a statement about.

The abelian Kan extension is arranged so that its underlying presheaf of types is *literally* the
set-valued one: a section over `X` is cut out of the product `∀ W, (j_total(W) ⟶ X) → G(W)` by
the same naturality condition as before, and that condition is closed under `0`, `+` and `-`
because each restriction map of `G` is additive. Writing the condition as an `AddSubgroup` of the
product supplies all the group axioms from `Pi.addCommGroup`, and keeps
`ranPresheafAb ⋙ forget Ab` definitionally equal to `ranPresheaf`. Consequently the sheaf
condition transports by `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` and the comparison
morphism is an isomorphism because `forget Ab` reflects isomorphisms.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]
  (G : Sheaf (situation J K).totalTopology Ab.{u})

/-- The underlying sheaf of sets of a sheaf of abelian groups on the total site. This is the
sheaf of sets that `CategoryTheory.SimplicialSiteSituation.IsCartesianAbSheaf` talks about. -/
abbrev forgetSheaf : Sheaf (situation J K).totalTopology (Type u) :=
  (sheafCompose ((situation J K).totalTopology) (forget Ab.{u})).obj G

/-! ### The abelian right Kan extension along `j_total` -/

/-- The sections over `X : C` of the right Kan extension of `G` along `j_total`, as a subgroup of
the product of the groups of sections of `G` over the objects of the total site charted over `X`:
the naturality condition cutting them out is closed under `0`, `+` and `-` because the
restriction maps of `G` are additive. -/
def ranSubgroupAb (X : C) : AddSubgroup (∀ W : Grothendieck (slices K),
    ((totalForget K).obj W ⟶ X) → (G.obj.obj (op W) : Type u)) where
  carrier := {s | ∀ {W W' : Grothendieck (slices K)} (θ : W' ⟶ W)
    (φ : (totalForget K).obj W ⟶ X),
    (forgetSheaf J K G).obj.map θ.op (s W φ) = s W' ((totalForget K).map θ ≫ φ)}
  zero_mem' {_ _} θ _ := map_zero (G.obj.map θ.op).hom
  add_mem' {_ _} ha hb {_ _} θ φ :=
    (map_add (G.obj.map θ.op).hom _ _).trans (congr_arg₂ (· + ·) (ha θ φ) (hb θ φ))
  neg_mem' {_} ha {_ _} θ φ :=
    (map_neg (G.obj.map θ.op).hom _).trans (congrArg Neg.neg (ha θ φ))

/-- The sections of the abelian Kan extension are the sections of the set-valued Kan extension of
the underlying sheaf of sets. -/
theorem coe_ranSubgroupAb (X : C) :
    (ranSubgroupAb J K G X : Type u) = ranSection J K (forgetSheaf J K G) X :=
  rfl

/-- The right Kan extension of `G` along `j_total`, as a presheaf of abelian groups on `C`. -/
def ranPresheafAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (ranSubgroupAb J K G X.unop)
  map {_ _} f := ConcreteCategory.ofHom
    { toFun s := ⟨fun W φ => s.1 W (φ ≫ f.unop), fun {_ _} θ φ =>
        (s.2 θ (φ ≫ f.unop)).trans (congrArg (s.1 _) (Category.assoc _ _ _).symm)⟩
      map_zero' := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl }
  map_id _ := ConcreteCategory.hom_ext _ _ fun s =>
    Subtype.ext (funext fun W => funext fun φ => congrArg (s.1 W) (Category.comp_id φ))
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun s =>
    Subtype.ext (funext fun W => funext fun _ => congrArg (s.1 W) (Category.assoc _ _ _).symm)

/-- The abelian Kan extension has the set-valued Kan extension as underlying presheaf of types. -/
theorem ranPresheafAb_comp_forget :
    ranPresheafAb J K G ⋙ forget Ab.{u} = ranPresheaf J K (forgetSheaf J K G) :=
  rfl

/-- **The right Kan extension along `j_total` of a sheaf of abelian groups on the total site is a
sheaf.** Its underlying presheaf of types is the set-valued Kan extension, which is a sheaf by
`CategoryTheory.SimplicialSemiRepresentable.isSheaf_ranPresheaf`, and the forgetful functor of
`Ab` preserves limits and reflects isomorphisms. -/
theorem isSheaf_ranPresheafAb : Presheaf.IsSheaf J (ranPresheafAb J K G) :=
  (Presheaf.isSheaf_iff_isSheaf_forget J (ranPresheafAb J K G) (forget Ab.{u})).2
    (isSheaf_ranPresheaf J K (forgetSheaf J K G))

/-- The comparison morphism from the restriction of the abelian Kan extension back to `G`:
evaluation of a section of the Kan extension over `j_total(W)` at the identity chart of `W`. -/
def ranEvAb : (totalForget K).op ⋙ ranPresheafAb J K G ⟶ G.obj where
  app W := ConcreteCategory.ofHom
    { toFun s := s.1 W.unop (𝟙 _)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality {_ W'} θ := ConcreteCategory.hom_ext _ _ fun s =>
    (congrArg (s.1 W'.unop) ((Category.id_comp ((totalForget K).map θ.unop)).trans
      (Category.comp_id ((totalForget K).map θ.unop)).symm)).trans
      (s.2 θ.unop (𝟙 _)).symm

/-! ### A rigid abelian sheaf is an inverse image -/

section EssImage

variable {J K G}

/-- **A rigid sheaf of abelian groups on the total site is an inverse image along `j_total`.**
The comparison morphism is bijective on sections by
`CategoryTheory.SimplicialSemiRepresentable.ranEv_app_bijective` applied to the underlying sheaf
of sets, hence an isomorphism of abelian groups because `forget Ab` reflects isomorphisms. -/
theorem essImage_of_rigidAb (hlf : (totalForget K).IsLocallyFull J)
    (hrig : ∀ {W U : Grothendieck (slices K)} (ψ ψ' : W ⟶ U),
      (totalForget K).map ψ = (totalForget K).map ψ' →
        (forgetSheaf J K G).obj.map ψ.op = (forgetSheaf J K G).obj.map ψ'.op)
    (hvert : ∀ {W U : Grothendieck (slices K)} (π : W ⟶ U),
      IsIso ((totalForget K).map π) → IsIso ((forgetSheaf J K G).obj.map π.op)) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
      ((situation J K).totalTopology) J).essImage G := by
  have happ : ∀ W, IsIso ((ranEvAb J K G).app W) := by
    intro W
    have : IsIso ((forget Ab.{u}).map ((ranEvAb J K G).app W)) :=
      (isIso_iff_bijective _).2 (ranEv_app_bijective hlf hrig hvert W.unop)
    exact isIso_of_reflects_iso _ (forget Ab.{u})
  refine ⟨⟨ranPresheafAb J K G, isSheaf_ranPresheafAb J K G⟩, ⟨?_⟩⟩
  refine (fullyFaithfulSheafToPresheaf ((situation J K).totalTopology) Ab.{u}).preimageIso ?_
  exact NatIso.ofComponents (fun W => @asIso _ _ _ _ ((ranEvAb J K G).app W) (happ W))
    fun θ => (ranEvAb J K G).naturality θ

end EssImage

/-! ### Stacks 0D8E: essential surjectivity onto the cartesian abelian sheaves -/

section Hypercovering

variable [HasEqualizers C] [HasPullbacks C]

/-- **Stacks 0D8E (2), essential surjectivity onto the cartesian abelian sheaves.** For a
hypercovering `K` of the final presheaf, every cartesian sheaf of abelian groups on the total
site `(C/K)_total` lies in the essential image of restriction along the localization functor
`j_total`. -/
theorem essImage_of_isCartesianAbSheaf (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u})
    (hG : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G) :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
      ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
      P.toGrothendieck).essImage G :=
  essImage_of_rigidAb (isLocallyFull_totalForget P H)
    (fun ψ ψ' h => map_eq_of_totalForget_map_eq P H
      (forgetSheaf P.toGrothendieck H.toSimplicialObject G) hG ψ ψ' h)
    (fun π h => isIso_map_of_isIso_totalForget_map P.toGrothendieck H.toSimplicialObject
      (forgetSheaf P.toGrothendieck H.toSimplicialObject G) hG π h)

/-- **Stacks 0D8E (2), the essential image is exactly the cartesian abelian sheaves.** One
inclusion is `isCartesianAbSheaf_of_mem_essImage`, the other is
`essImage_of_isCartesianAbSheaf`. -/
@[stacks 0D8E "part (2): essential image = cartesian abelian sheaves"]
theorem mem_essImage_iff_isCartesianAbSheaf' (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u}) :
    ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
        ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
        P.toGrothendieck).essImage G ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G :=
  ⟨isCartesianAbSheaf_of_mem_essImage P.toGrothendieck H.toSimplicialObject,
    essImage_of_isCartesianAbSheaf P H G⟩

/-- **Stacks 0D8E (2), `a⁻¹ a_* F = F` for cartesian `F`.** For a cartesian sheaf of abelian
groups `F` on the total site the canonical map `a⁻¹ a_* F ⟶ F` is an isomorphism. This is the
half of "`a_*` is a quasi-inverse" that holds on the cartesian abelian sheaves: `a⁻¹` is fully
faithful, so its counit is invertible exactly on its essential image, and
`essImage_of_isCartesianAbSheaf` puts `F` there. -/
@[stacks 0D8E "part (2): a^{-1} a_* F = F for cartesian abelian F"]
theorem isIso_abelianCounit_app_hypercovering' (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u})
    (hG : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G) :
    IsIso ((abelianTotalAdjunction P.toGrothendieck
      H.toSimplicialObject).counit.app G) :=
  (isIso_abelianCounit_app_iff_mem_essImage_of_isLocallyFull P.toGrothendieck
    H.toSimplicialObject (isCoverDense_totalForget P H) (isLocallyFull_totalForget P H) G).mpr
    (essImage_of_isCartesianAbSheaf P H G hG)

end Hypercovering

end CategoryTheory.SimplicialSemiRepresentable

end
