module

public import StacksFrontier.Cotangent.SheavesOfRings.StalkwiseChangeOfBase
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafLocalIso
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The stalk of the cotangent complex of sheaves of rings on a space, on germs

Let `X` be a topological space and `g : A ⟶ B` a homomorphism of sheaves of commutative rings on
`X`. At a point `x`, the stalk of `L_{B/A}` is identified with `L_{B_x/A_x}`:

`(L_{B/A})_x ≅ (U ↦ L_{B(U)/A(U)})_x ≅ L_{B_x/A_x}`,

the first isomorphism because `L_{B/A}` is the sheafification of the sectionwise complex
(Tag 08SX, `CategoryTheory.Sheaf.W_sectionwiseCotangentPresheafComplexComparison_f`), the second
because the cotangent complex commutes with directed colimits (Tag 08S9,
`CategoryTheory.Sheaf.isIso_stalkCotangentComplex`). This file names the composite, as an
isomorphism of complexes of abelian groups, and records the two facts about it that the proof of
Tag 08T3 needs:

* on the germ of the canonical image of an element `t` of `L_{B(U)/A(U)}` it is the map of the
  germ square `(A(U) → A_x, B(U) → B_x)` applied to `t`;
* it is semilinear over the germ map `B(U) → B_x`: the germ of `c • r` goes to the germ of `c`
  times the image of the germ of `r`.

## Main definitions

* `CategoryTheory.Sheaf.cotangentComplexStalkAbIso`: the isomorphism
  `(L_{B/A})_x ≅ L_{B_x/A_x}` of complexes of abelian groups.

## Main results

* `CategoryTheory.Sheaf.cotangentComplexStalkAbIso_hom_germ`: its value on the germ of the image
  of a sectionwise element.
* `CategoryTheory.Sheaf.cotangentComplexStalkAbIso_hom_germ_smul`: its semilinearity.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (g : A ⟶ B) (x : X)

/-- The stalk at `x` of the canonical map from the sectionwise complex `U ↦ L_{B(U)/A(U)}` to
`L_{B/A}`, as a map of complexes of abelian groups. -/
abbrev sectionwiseStalkComparison :=
  ((TopCat.Presheaf.stalkAb x).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (sectionwiseCotangentPresheafComplexComparison (Opens.grothendieckTopology X) g)

/-- The stalk of the canonical map from the sectionwise complex is bijective in every degree,
because the canonical map is inverted by sheafification. -/
theorem bijective_sectionwiseStalkComparison_f (k : ℤ) :
    Function.Bijective ((sectionwiseStalkComparison g x).f k) := by
  have hW := W_sectionwiseCotangentPresheafComplexComparison_f (Opens.grothendieckTopology X) g k
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hW
  obtain ⟨h₁, h₂⟩ := hW
  exact TopCat.Presheaf.bijective_stalkFunctor_map_of_isLocallyBijective _ x

/-- The stalk of the canonical map from the sectionwise complex to `L_{B/A}` is an isomorphism of
complexes of abelian groups. -/
instance isIso_sectionwiseStalkComparison : IsIso (sectionwiseStalkComparison g x) := by
  have : ∀ k, IsIso ((sectionwiseStalkComparison g x).f k) := fun k =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_sectionwiseStalkComparison_f g x k)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The stalk of the cotangent complex of sheaves of rings on a space, as complexes of abelian
groups.** `(L_{B/A})_x ≅ L_{B_x/A_x}`: the inverse of the stalk of the canonical map from the
sectionwise complex, followed by the identification of the stalk of the sectionwise complex
with `L_{B_x/A_x}` of Tag 08S9. -/
def cotangentComplexStalkAbIso :
    ((TopCat.Presheaf.stalkAb x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplexAb (Opens.grothendieckTopology X) g)) ≅
      CommAlgCat.cotangentComplexAb.{u, u} (stalkRing x A) (stalkAlgebra g x) :=
  (asIso (sectionwiseStalkComparison g x)).symm ≪≫
    @asIso _ _ _ _ (stalkCotangentComplex g x) (isIso_stalkCotangentComplex g x)

/-- On the germ of the canonical image of an element `t` of `L_{B(U)/A(U)}`, the identification
`(L_{B/A})_x ≅ L_{B_x/A_x}` is the map of the germ square applied to `t`. -/
theorem cotangentComplexStalkAbIso_hom_germ (k : ℤ) (U : Opens X) (hx : x ∈ U)
    (t : ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) g).X k).obj
      (op U)) :
    (cotangentComplexStalkAbIso g x).hom.f k
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((cotangentComplexAb (Opens.grothendieckTopology X) g).X k).obj U x hx
          (((sectionwiseCotangentPresheafComplexComparison (Opens.grothendieckTopology X)
            g).f k).app (op U) t)) =
      (CommAlgCat.cotangentComplexAbMap (germSquare g x (OrderDual.toDual ⟨U, hx⟩))).f k t := by
  have h₁ : (sectionwiseStalkComparison g x).f k
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) g).X k) U x hx t) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((cotangentComplexAb (Opens.grothendieckTopology X) g).X k).obj U x hx
          (((sectionwiseCotangentPresheafComplexComparison (Opens.grothendieckTopology X)
            g).f k).app (op U) t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx _ t
  rw [← h₁]
  change (stalkCotangentComplex g x).f k ((inv (sectionwiseStalkComparison g x)).f k
    ((sectionwiseStalkComparison g x).f k _)) = _
  have h₂ : (inv (sectionwiseStalkComparison g x)).f k
      ((sectionwiseStalkComparison g x).f k
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) g).X k) U x hx t)) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) g).X k)
          U x hx t := by
    have e : (sectionwiseStalkComparison g x).f k ≫ (inv (sectionwiseStalkComparison g x)).f k =
        𝟙 _ := by
      rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
    exact ConcreteCategory.congr_hom e _
  rw [h₂]
  exact ConcreteCategory.congr_hom (stalkCotangentTerm_germ g x k (OrderDual.toDual ⟨U, hx⟩)) t

/-- **The identification `(L_{B/A})_x ≅ L_{B_x/A_x}` is semilinear over the germ map.** For a
section `c` of `B` and a section `r` of a term of `L_{B/A}` over a neighbourhood `U` of `x`, the
germ of `c • r` goes to the germ of `c` times the image of the germ of `r`. -/
theorem cotangentComplexStalkAbIso_hom_germ_smul (k : ℤ) (U : Opens X) (hx : x ∈ U)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj.obj (op U))
    (r : ((cotangentComplex (Opens.grothendieckTopology X) g).X k).val.obj (op U)) :
    (cotangentComplexStalkAbIso g x).hom.f k
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((cotangentComplexAb (Opens.grothendieckTopology X) g).X k).obj U x hx (c • r)) =
      (show ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A) (stalkAlgebra g x)).X k : Type u)
        from (germSquare g x (OrderDual.toDual ⟨U, hx⟩)).map c •
          (show ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A) (stalkAlgebra g x)).X k :
              Type u) from (cotangentComplexStalkAbIso g x).hom.f k
            (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
              ((cotangentComplexAb (Opens.grothendieckTopology X) g).X k).obj U x hx r))) := by
  let J := Opens.grothendieckTopology X
  let P := (sectionwiseCotangentPresheafComplex J g).X k
  let L := ((cotangentComplexAb J g).X k).obj
  let a := (sectionwiseCotangentPresheafComplexComparison J g).f k
  -- `r` agrees near `x` with the canonical image of a sectionwise element `t₂`.
  obtain ⟨ζ, hζ⟩ := (bijective_sectionwiseStalkComparison_f g x k).2
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L U x hx r)
  obtain ⟨W₁, hx₁, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq P ζ
  have hζ' : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L W₁ x hx₁ (a.app (op W₁) t) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L U x hx r :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W₁ x hx₁ a t).symm.trans hζ
  obtain ⟨W₂, hx₂, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq L x hx₁ hx _ _ hζ'
  let t₂ : (sectionwiseCotangentTerm J g k).obj (op W₂) := P.map i₁.op t
  let c₂ : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj.obj (op W₂) :=
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj.map i₂.op c
  let r₂ : ((cotangentComplex J g).X k).val.obj (op W₂) := L.map i₂.op r
  let cr₂ : ((cotangentComplex J g).X k).val.obj (op W₂) := L.map i₂.op (c • r)
  let a₂ := (sectionwiseCotangentTermComparison J g k).app (op W₂)
  have hnat : L.map i₁.op (a.app (op W₁) t) = a.app (op W₂) t₂ :=
    (ConcreteCategory.congr_hom (a.naturality i₁.op) t).symm
  -- the restriction of `r` is the image of `t₂`
  have hr : r₂ = a₂ t₂ := he.symm.trans hnat
  -- the restriction of `c • r` is the image of `c₂ • t₂`
  have hcr : cr₂ = a₂ (c₂ • t₂) := by
    have h₁ : cr₂ = c₂ • r₂ := ((cotangentComplex J g).X k).val.map_smul i₂.op c r
    have h₂ : a₂ (c₂ • t₂) = c₂ • a₂ t₂ := a₂.hom.map_smul c₂ t₂
    rw [h₁, hr, h₂]
  have germ_eq : ∀ (s : L.obj (op U)) (s' : L.obj (op W₂)), L.map i₂.op s = s' →
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L U x hx s =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L W₂ x hx₂ s' := fun s s' h =>
    (TopCat.Presheaf.germ_res_apply L i₂ x hx₂ s).symm.trans
      (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L W₂ x hx₂) h)
  have gr := germ_eq r (a.app (op W₂) t₂) hr
  have gcr := germ_eq (c • r) (a.app (op W₂) (c₂ • t₂)) hcr
  -- semilinearity of the map of the germ square
  have hsq : (CommAlgCat.cotangentComplexAbMap (germSquare g x (OrderDual.toDual ⟨W₂, hx₂⟩))).f k
      (c₂ • t₂) = (show ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A)
        (stalkAlgebra g x)).X k : Type u) from
          (germSquare g x (OrderDual.toDual ⟨W₂, hx₂⟩)).map c₂ •
            (show ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A)
              (stalkAlgebra g x)).X k : Type u) from
              (CommAlgCat.cotangentComplexAbMap
                (germSquare g x (OrderDual.toDual ⟨W₂, hx₂⟩))).f k t₂)) :=
    ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
      (germSquare g x (OrderDual.toDual ⟨W₂, hx₂⟩))).f k).hom.map_smul c₂ t₂
  have hc : (germSquare g x (OrderDual.toDual ⟨W₂, hx₂⟩)).map c₂ =
      (germSquare g x (OrderDual.toDual ⟨U, hx⟩)).map c :=
    TopCat.Presheaf.germ_res_apply B.obj i₂ x hx₂ c
  have hM : (show ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A)
        (stalkAlgebra g x)).X k : Type u) from
        (CommAlgCat.cotangentComplexAbMap (germSquare g x (OrderDual.toDual ⟨W₂, hx₂⟩))).f k t₂) =
      (show ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A) (stalkAlgebra g x)).X k :
          Type u) from (cotangentComplexStalkAbIso g x).hom.f k
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L U x hx r)) :=
    (cotangentComplexStalkAbIso_hom_germ g x k W₂ hx₂ t₂).symm.trans
      (congrArg (fun z => (cotangentComplexStalkAbIso g x).hom.f k z) gr.symm)
  exact ((congrArg (fun z => (cotangentComplexStalkAbIso g x).hom.f k z) gcr).trans
    (cotangentComplexStalkAbIso_hom_germ g x k W₂ hx₂ (c₂ • t₂))).trans
    (hsq.trans (congrArg₂ (fun (s : (stalkAlgebra g x : Type u))
      (z : ((CommAlgCat.cotangentComplex.{u, u} (stalkRing x A) (stalkAlgebra g x)).X k :
        Type u)) => s • z) hc hM))

end CategoryTheory.Sheaf

end
