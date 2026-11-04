module

public import Mathlib.Algebra.Group.MinimalAxioms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsomSupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

/-!
# The sheaf of automorphisms and the torsor of isomorphisms

Let `(C, J)` be a site and let `F`, `G` be sheaves on it with values in a category `A`. The sheaf
of sets `Isom(G, G)`, whose sections over `X` are the automorphisms of the restriction `G|_X` to
the slice site `C/X`, is a sheaf of groups under composition, the sheaf of automorphisms
`Aut(G)`. It acts on `Isom(F, G)` by composition on the target, and the action is simply
transitive on every nonempty set of sections: two isomorphisms `F|_X ≅ G|_X` differ by a unique
automorphism of `G|_X`. So `Isom(F, G)` is a pseudo-torsor under `Aut(G)`, which is a torsor
exactly when `F` and `G` are locally isomorphic.

## Main definitions

* `Stacks.ConstantSheaf.sheafAut`: the sheaf of groups `Aut(G)`.
* `Stacks.ConstantSheaf.sheafIsomPseudoTorsor`: `Isom(F, G)` as a pseudo-torsor under `Aut(G)`.

## Implementation notes

The product of two sections `g` and `h` of `Aut(G)` is the composite `h ≫ g`, so that `g * h`
acts by first applying `h`; this is the convention of `CategoryTheory.Aut`. A section `g` of
`Aut(G)` acts on a section `s` of `Isom(F, G)` by `s ≫ g`.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v u' v'

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

section Group

variable (G : Sheaf J A) (X : Cᵒᵖ)

/-- A section of `Isom(F, G)` is an isomorphism. -/
theorem isIso_sheafIsom_val {F : Sheaf J A} (s : (sheafIsom J A F G).obj.obj X) : IsIso s.1 :=
  s.2

/-- The group structure on the automorphisms of `G|_X`: the product `g * h` is `h ≫ g`. -/
instance sheafIsomGroup : Group ((sheafIsom J A G G).obj.obj X) :=
  letI : Mul ((sheafIsom J A G G).obj.obj X) :=
    ⟨fun g h => ⟨h.1 ≫ g.1, IsIso.comp_isIso' h.2 g.2⟩⟩
  letI : One ((sheafIsom J A G G).obj.obj X) := ⟨⟨𝟙 _, IsIso.id _⟩⟩
  letI : Inv ((sheafIsom J A G G).obj.obj X) :=
    ⟨fun g => ⟨@inv _ _ _ _ g.1 g.2, @IsIso.inv_isIso _ _ _ _ g.1 g.2⟩⟩
  Group.ofLeftAxioms (fun _ _ _ => Subtype.ext (Category.assoc _ _ _).symm)
    (fun _ => Subtype.ext (Category.comp_id _))
    (fun g => Subtype.ext (@IsIso.hom_inv_id _ _ _ _ g.1 g.2))

/-- The product `g * h` of automorphisms of `G|_X` is the composite `h ≫ g`. -/
theorem sheafIsom_mul_val (g h : (sheafIsom J A G G).obj.obj X) : (g * h).1 = h.1 ≫ g.1 :=
  rfl

/-- The identity automorphism of `G|_X` is `𝟙`. -/
theorem sheafIsom_one_val : (1 : (sheafIsom J A G G).obj.obj X).1 = 𝟙 _ :=
  rfl

/-- The inverse of an automorphism of `G|_X` is its categorical inverse. -/
theorem sheafIsom_inv_val (g : (sheafIsom J A G G).obj.obj X) :
    g⁻¹.1 = @inv _ _ _ _ g.1 g.2 :=
  rfl

end Group

/-- The restriction maps of `Isom(F, G)` are restriction of local isomorphisms along
`CategoryTheory.Over.map`. -/
theorem sheafIsom_map_val {F G : Sheaf J A} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : (sheafIsom J A F G).obj.obj X) :
    ((sheafIsom J A F G).obj.map f s).1 = (J.overMapPullback A f.unop).map s.1 :=
  rfl

/-- **The sheaf of automorphisms** `Aut(G)` of a sheaf `G`: the sheaf of sets `Isom(G, G)` with
the group structure given by composition. -/
def sheafAut (G : Sheaf J A) : SheafOfGroups.{max u v v'} J where
  presheaf := (sheafIsom J A G G).obj
  isSheaf := (sheafIsom J A G G).property
  group X := sheafIsomGroup J A G X
  map_mul f g h := Subtype.ext ((J.overMapPullback A f.unop).map_comp h.1 g.1)

/-- **`Isom(F, G)` is a pseudo-torsor under `Aut(G)`**, the action being composition on the
target: two isomorphisms `F|_X ≅ G|_X` differ by a unique automorphism of `G|_X`. -/
def sheafIsomPseudoTorsor (F G : Sheaf J A) : PseudoTorsor.{max u v v'} (sheafAut J A G) where
  presheaf := (sheafIsom J A F G).obj
  isSheaf := (sheafIsom J A F G).property
  act _ g s := ⟨s.1 ≫ g.1, IsIso.comp_isIso' s.2 g.2⟩
  one_act _ s := Subtype.ext (Category.comp_id s.1)
  mul_act _ g h s := Subtype.ext (Category.assoc s.1 h.1 g.1).symm
  naturality f g s := Subtype.ext ((J.overMapPullback A f.unop).map_comp s.1 g.1)
  simplyTransitive _ _ s t := by
    have : IsIso s.1 := s.2
    refine ⟨⟨inv s.1 ≫ t.1, IsIso.comp_isIso' (IsIso.inv_isIso) t.2⟩,
      Subtype.ext (IsIso.hom_inv_id_assoc s.1 t.1), fun g hg => Subtype.ext ?_⟩
    change g.1 = inv s.1 ≫ t.1
    rw [← congrArg Subtype.val hg]
    exact (IsIso.inv_hom_id_assoc s.1 g.1).symm

/-- The underlying presheaf of the pseudo-torsor `sheafIsomPseudoTorsor F G` is `Isom(F, G)`. -/
theorem sheafIsomPseudoTorsor_presheaf (F G : Sheaf J A) :
    (sheafIsomPseudoTorsor J A F G).presheaf = (sheafIsom J A F G).obj :=
  rfl

end Stacks.ConstantSheaf

end
