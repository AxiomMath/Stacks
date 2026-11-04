module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsomNaturality
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.CategoryTheory.Sites.IsomSheafGlobalSections

/-!
# From the module `Isom` system to the tower of isomorphisms of constant sheaves

Let `(C, J)` be a site with a terminal object `T`, let `Λ` be a commutative ring and let
`Mt : ℕᵒᵖ ⥤ ModuleCat Λ` be a tower of finitely presented `Λ`-modules whose self-isomorphisms
reduce along the transition maps. Write `A = Mt ⋙ (·)̲` for the tower of constant sheaves.

This file compares two inverse systems of sets:

* the global sections `n ↦ Γ(T, Isom_Λ(Mₙ, Mₙ)̲)` of the constant sheaves on the sets of
  self-isomorphisms of the modules, and
* `n ↦ (Aₙ ≅ Aₙ)`, the tower `CategoryTheory.Functor.isoTower` of sets of self-isomorphisms of
  the constant sheaves.

The comparison is a *bijection* at every level, by Stacks Tag 093T (2) and by the identification
of the isomorphisms of two sheaves with the sections of `Isom` over a terminal object. Hence the
Mittag-Leffler condition for the module system — which is Stacks Tag 09BB — transfers to the tower
of isomorphisms of constant sheaves, which is the remaining input of
`CategoryTheory.Functor.nonempty_natIso_of_isMittagLeffler_isoTower` and so of Stacks Tag 09BV.

## Main definitions

* `Stacks.ConstantSheaf.constantGlobalSections`: the functor of types `S ↦ Γ(T, S̲)`.
* `Stacks.ConstantSheaf.selfIsomSystem`: the inverse system `n ↦ (Mₙ ≃ₗ[Λ] Mₙ)` built from a
  family of reduction maps on self-isomorphisms.
* `Stacks.ConstantSheaf.isoTowerComparison`: the comparison, as a morphism of inverse systems.

## Main results

* `Stacks.ConstantSheaf.bijective_isoTowerComparisonApp`: the comparison is bijective at every
  level.
* `Stacks.ConstantSheaf.isMittagLeffler_isoTower_constantSheaf`: the tower of self-isomorphisms of
  the constant sheaves is Mittag-Leffler as soon as the module system is.

## Implementation notes

The naturality square is the delicate point, and it is delicate for two independent reasons.

First, the transition map of the target is the *descended* isomorphism supplied by
`CategoryTheory.Functor.DescendsIsos`, not a composite, so the square cannot be computed: it is
recognized through `CategoryTheory.Functor.DescendsIsos.unique`, which says that an isomorphism
making the descent square commute is unique when the transition maps of the source tower are
epimorphisms. The square to be exhibited is then one of morphisms of sheaves.

Second, that square of morphisms of sheaves is obtained from
`Stacks.ConstantSheaf.constantSheafIsomHom_naturality` by applying restriction to the slice site
over `T`, which is faithful, and the evaluation of that naturality statement at `T` is carried out
in term mode. Rewriting the identity morphisms away inside it by `rw` produces a target which is
not type-correct at `implicit` transparency, the sections of `Isom` having two spellings whose
`Quiver` instances are reached by different paths; the identities are therefore cancelled by
`Stacks.ConstantSheaf.conj_square_of_map_id_square`, a statement about an abstract functor in
which no such spelling occurs.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w x y

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  {T : C}

/-- **The global sections of a constant sheaf, as a functor of types**: `S ↦ Γ(T, S̲)`. The
Mittag-Leffler condition passes to the image of an inverse system of sets under it, by
`CategoryTheory.Functor.IsMittagLeffler.comp_type`. -/
abbrev constantGlobalSections : Type (max u v x) ⥤ Type (max u v x) :=
  constantSheaf J (Type (max u v x)) ⋙
    (sheafSections J (Type (max u v x))).obj (op T)

/-- The isomorphism of two sheaves attached to a section of `Isom` over a terminal object has, for
underlying morphism of the restrictions to the slice site, that very section. -/
theorem overPullback_map_isoEquivSheafIsomObjIsTerminal_symm_hom (A : Type*) [Category A]
    (hT : IsTerminal T) (F G : Sheaf J A) (z : (sheafIsom J A F G).obj.obj (op T)) :
    (J.overPullback A T).map
        ((isoEquivSheafIsomObjIsTerminal J A hT F G).symm z).hom = z.1 := by
  rw [← isoEquivSheafIsomObjIsTerminal_coe J A hT F G, Equiv.apply_symm_apply]

/-- An invertible section of the internal hom, pushed into the internal hom and composed there
with the restrictions of two morphisms, is the composite of the three. -/
theorem sheafIsomIncl_sheafHomMap_hom_app_apply {A : Type*} [Category A] {F F' G G' : Sheaf J A}
    (u : F' ⟶ F) (w : G ⟶ G') (X : Cᵒᵖ) (z : (sheafIsom J A F G).obj.obj X) :
    (sheafIsomIncl J F G ≫ sheafHomMap J u w).hom.app X z =
      (J.overPullback A X.unop).map u ≫ z.1 ≫ (J.overPullback A X.unop).map w :=
  rfl

/-- A commuting square whose two outer edges are the images of identities is a commuting square of
the two inner edges with the image of one morphism. Stated for an abstract functor because the
cancellation is applied to a square in which the morphisms carry two spellings of the sections of
`Isom`, and rewriting there is not type-correct at `implicit` transparency. -/
theorem conj_square_of_map_id_square {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {U V : D} (g : U ⟶ V) (a : F.obj U ⟶ F.obj U) (b : F.obj V ⟶ F.obj V)
    (h : F.map (𝟙 U) ≫ a ≫ F.map g = F.map g ≫ b ≫ F.map (𝟙 V)) :
    F.map g ≫ b = a ≫ F.map g := by
  rw [F.map_id, F.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

section Square

variable (M N : ModuleCat.{max u v x} Λ)
  [Module.FinitePresentation Λ (M : Type (max u v x))]
  [Module.FinitePresentation Λ (N : Type (max u v x))]

omit [Module.FinitePresentation Λ (M : Type (max u v x))]
  [Module.FinitePresentation Λ (N : Type (max u v x))] in
/-- The naturality of the comparison of Tag 093T (2), evaluated on a global section over a
terminal object: the form in which it comes out of
`Stacks.ConstantSheaf.constantSheafIsomHom_naturality`, with the two identity morphisms of that
statement still in place. -/
theorem constantSheafIsomHom_terminal_square_mapId (_hT : IsTerminal T) (p : M ⟶ N)
    (red : ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x))) →
      ((N : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))))
    (hred : ∀ e, ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫ p =
      p ≫ ModuleCat.ofHom (red e).toLinearMap)
    (s : (constantGlobalSections.{u, v, x} J (T := T)).obj
      ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x)))) :
    (J.overPullback (ModuleCat.{max u v x} Λ) T).map
          (𝟙 ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)) ≫
        (((constantSheafIsomHom J Λ M M).hom.app (op T)) s).1 ≫
          (J.overPullback (ModuleCat.{max u v x} Λ) T).map
            ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) =
      (J.overPullback (ModuleCat.{max u v x} Λ) T).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) ≫
        (((constantSheafIsomHom J Λ N N).hom.app (op T))
            ((constantGlobalSections.{u, v, x} J (T := T)).map (↾red) s)).1 ≫
          (J.overPullback (ModuleCat.{max u v x} Λ) T).map
            (𝟙 ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)) :=
  congrArg
    (fun φ : (constantSheaf J (Type (max u v x))).obj
        ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x))) ⟶
      sheafHom ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) => φ.hom.app (op T) s)
    (constantSheafIsomHom_naturality J Λ M N p red hred)

omit [Module.FinitePresentation Λ (M : Type (max u v x))]
  [Module.FinitePresentation Λ (N : Type (max u v x))] in
/-- **The square the descended isomorphism has to make commute**: on the restrictions to the slice
site over a terminal object `T`, the global section `s` of `Isom_Λ(M, M)̲` and its reduction
commute with the constant sheaf of `p : M ⟶ N`. -/
theorem constantSheafIsomHom_terminal_square (hT : IsTerminal T) (p : M ⟶ N)
    (red : ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x))) →
      ((N : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))))
    (hred : ∀ e, ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫ p =
      p ≫ ModuleCat.ofHom (red e).toLinearMap)
    (s : (constantGlobalSections.{u, v, x} J (T := T)).obj
      ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x)))) :
    (J.overPullback (ModuleCat.{max u v x} Λ) T).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) ≫
        (((constantSheafIsomHom J Λ N N).hom.app (op T))
          ((constantGlobalSections.{u, v, x} J (T := T)).map (↾red) s)).1 =
      (((constantSheafIsomHom J Λ M M).hom.app (op T)) s).1 ≫
        (J.overPullback (ModuleCat.{max u v x} Λ) T).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) :=
  conj_square_of_map_id_square (J.overPullback (ModuleCat.{max u v x} Λ) T)
    ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) _ _
    (constantSheafIsomHom_terminal_square_mapId J Λ M N hT p red hred s)

end Square

section System

variable (Mt : ℕᵒᵖ ⥤ ModuleCat.{y} Λ)

/-- **The inverse system of sets of self-isomorphisms of a tower of modules**, whose transition
maps are a prescribed family of reductions. -/
def selfIsomSystem
    (tr : ∀ n : ℕ, (((Mt.obj (op (n + 1))) : Type y) ≃ₗ[Λ] ((Mt.obj (op (n + 1))) : Type y)) →
      (((Mt.obj (op n)) : Type y) ≃ₗ[Λ] ((Mt.obj (op n)) : Type y))) :
    ℕᵒᵖ ⥤ Type y :=
  Functor.ofOpSequence
    (X := fun n : ℕ => (((Mt.obj (op n)) : Type y) ≃ₗ[Λ] ((Mt.obj (op n)) : Type y)))
    (fun n => ↾(tr n))

end System

section Tower

variable (Mt : ℕᵒᵖ ⥤ ModuleCat.{max u v x} Λ)

/-- **The comparison at one level**: a global section of `Isom_Λ(Mₙ, Mₙ)̲` over the terminal object
is read, through Tag 093T (2), as a global section of `Isom(Mₙ̲, Mₙ̲)`, hence as a
self-isomorphism of the constant sheaf `Mₙ̲`. -/
def isoTowerComparisonApp
    (hfp : ∀ n : ℕ, Module.FinitePresentation Λ ((Mt.obj (op n) : Type (max u v x))))
    (hT : IsTerminal T) (n : ℕ) :
    (constantGlobalSections.{u, v, x} J (T := T)).obj
        (((Mt.obj (op n)) : Type (max u v x)) ≃ₗ[Λ] ((Mt.obj (op n)) : Type (max u v x))) →
      ((Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)).obj (op n) ≅
        (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)).obj (op n)) :=
  haveI := hfp n
  fun s => (isoEquivSheafIsomObjIsTerminal J (ModuleCat.{max u v x} Λ) hT _ _).symm
    ((constantSheafIsomHom J Λ (Mt.obj (op n)) (Mt.obj (op n))).hom.app (op T) s)

/-- The isomorphism of constant sheaves produced by the comparison has, for underlying morphism of
the restrictions to the slice site over `T`, the section of `Isom` the comparison came from. -/
theorem overPullback_map_isoTowerComparisonApp_hom
    (hfp : ∀ n : ℕ, Module.FinitePresentation Λ ((Mt.obj (op n) : Type (max u v x))))
    (hT : IsTerminal T) (n : ℕ)
    (s : (constantGlobalSections.{u, v, x} J (T := T)).obj
      (((Mt.obj (op n)) : Type (max u v x)) ≃ₗ[Λ] ((Mt.obj (op n)) : Type (max u v x)))) :
    (J.overPullback (ModuleCat.{max u v x} Λ) T).map
        (isoTowerComparisonApp J Λ Mt hfp hT n s).hom =
      haveI := hfp n
      (((constantSheafIsomHom J Λ (Mt.obj (op n)) (Mt.obj (op n))).hom.app (op T)) s).1 :=
  have := hfp n
  overPullback_map_isoEquivSheafIsomObjIsTerminal_symm_hom J (ModuleCat.{max u v x} Λ) hT _ _ _

/-- **The comparison is bijective at every level**: Tag 093T (2) makes it a bijection onto the
sections of `Isom` over the terminal object, and those are the isomorphisms of the two sheaves. -/
theorem bijective_isoTowerComparisonApp
    (hfp : ∀ n : ℕ, Module.FinitePresentation Λ ((Mt.obj (op n) : Type (max u v x))))
    (hT : IsTerminal T) (n : ℕ) :
    Function.Bijective (isoTowerComparisonApp J Λ Mt hfp hT n) := by
  have := hfp n
  have hiso : IsIso (((sheafSections J (Type (max u v x))).obj (op T)).map
      (constantSheafIsomHom J Λ (Mt.obj (op n)) (Mt.obj (op n)))) := Functor.map_isIso _ _
  exact (isoEquivSheafIsomObjIsTerminal J (ModuleCat.{max u v x} Λ) hT _ _).symm.bijective.comp
    ((isIso_iff_bijective _).1 hiso)

/-- **The square the descended isomorphism has to make commute**, in the tower of constant
sheaves: the comparison carries a global section of `Isom_Λ(Mₙ₊₁, Mₙ₊₁)̲` and its reduction to two
self-isomorphisms of constant sheaves commuting with the transition map of the tower. Lifted from
`Stacks.ConstantSheaf.constantSheafIsomHom_terminal_square` through the faithfulness of
restriction to the slice site over the terminal object. -/
theorem isoTowerComparisonApp_square
    (tr : ∀ n : ℕ, (((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x))) →
      (((Mt.obj (op n)) : Type (max u v x)) ≃ₗ[Λ] ((Mt.obj (op n)) : Type (max u v x))))
    (hfp : ∀ n : ℕ, Module.FinitePresentation Λ ((Mt.obj (op n) : Type (max u v x))))
    (hT : IsTerminal T)
    (htr : ∀ (n : ℕ) (e : ((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x))),
      ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫
          Mt.map (homOfLE (Nat.le_add_right n 1)).op =
        Mt.map (homOfLE (Nat.le_add_right n 1)).op ≫ ModuleCat.ofHom (tr n e).toLinearMap)
    (n : ℕ)
    (s : (constantGlobalSections.{u, v, x} J (T := T)).obj
      (((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x)))) :
    (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        (isoTowerComparisonApp J Λ Mt hfp hT n
          ((constantGlobalSections.{u, v, x} J (T := T)).map (↾(tr n)) s)).hom =
      (isoTowerComparisonApp J Λ Mt hfp hT (n + 1) s).hom ≫
        (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)).map
          (homOfLE (Nat.le_add_right n 1)).op := by
  have := hfp n
  have := hfp (n + 1)
  refine (overPullbackFullyFaithfulOfIsTerminal J (ModuleCat.{max u v x} Λ) hT).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    overPullback_map_isoTowerComparisonApp_hom, overPullback_map_isoTowerComparisonApp_hom]
  exact constantSheafIsomHom_terminal_square J Λ (Mt.obj (op (n + 1))) (Mt.obj (op n)) hT
    (Mt.map (homOfLE (Nat.le_add_right n 1)).op) (tr n) (htr n) s

/-- **The comparison as a morphism of inverse systems.** The naturality square is recognized, not
computed: the transition map of the target is the descended isomorphism, which
`CategoryTheory.Functor.DescendsIsos.unique` pins down by the square it makes commute, and that
square is `Stacks.ConstantSheaf.isoTowerComparisonApp_square`. -/
def isoTowerComparison
    (tr : ∀ n : ℕ, (((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x))) →
      (((Mt.obj (op n)) : Type (max u v x)) ≃ₗ[Λ] ((Mt.obj (op n)) : Type (max u v x))))
    (hfp : ∀ n : ℕ, Module.FinitePresentation Λ ((Mt.obj (op n) : Type (max u v x))))
    (hT : IsTerminal T)
    (htr : ∀ (n : ℕ) (e : ((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x))),
      ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫
          Mt.map (homOfLE (Nat.le_add_right n 1)).op =
        Mt.map (homOfLE (Nat.le_add_right n 1)).op ≫ ModuleCat.ofHom (tr n e).toLinearMap)
    (hepi : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n),
      Epi ((Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)).map f))
    (hAA : Functor.DescendsIsos (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ))
      (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ))) :
    selfIsomSystem Λ Mt tr ⋙ constantGlobalSections.{u, v, x} J (T := T) ⟶
      Functor.isoTower (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ))
        (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)) hepi hAA :=
  NatTrans.ofOpSequence (fun n => ↾(isoTowerComparisonApp J Λ Mt hfp hT n)) (fun n => by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    have hmap : (selfIsomSystem Λ Mt tr).map (homOfLE (Nat.le_add_right n 1)).op = ↾(tr n) :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [Functor.comp_map, hmap]
    exact (Functor.DescendsIsos.unique hepi (homOfLE (Nat.le_add_right n 1)).op
      (hAA (homOfLE (Nat.le_add_right n 1)).op
        (isoTowerComparisonApp J Λ Mt hfp hT (n + 1) s)).choose_spec
      (isoTowerComparisonApp_square J Λ Mt tr hfp hT htr n s)).symm)

/-- **The tower of self-isomorphisms of the constant sheaves of a tower of modules is
Mittag-Leffler as soon as the tower of self-isomorphisms of the modules is.** The sets of
self-isomorphisms of the modules pass to global sections of their constant sheaves without losing
the condition (`CategoryTheory.Functor.IsMittagLeffler.comp_type`), and there the comparison with
the sheaf-level tower is bijective, so
`CategoryTheory.Functor.isMittagLeffler_of_surjective_natTrans` transfers it. -/
theorem isMittagLeffler_isoTower_constantSheaf
    (tr : ∀ n : ℕ, (((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x))) →
      (((Mt.obj (op n)) : Type (max u v x)) ≃ₗ[Λ] ((Mt.obj (op n)) : Type (max u v x))))
    (hfp : ∀ n : ℕ, Module.FinitePresentation Λ ((Mt.obj (op n) : Type (max u v x))))
    (hT : IsTerminal T)
    (htr : ∀ (n : ℕ) (e : ((Mt.obj (op (n + 1))) : Type (max u v x)) ≃ₗ[Λ]
        ((Mt.obj (op (n + 1))) : Type (max u v x))),
      ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫
          Mt.map (homOfLE (Nat.le_add_right n 1)).op =
        Mt.map (homOfLE (Nat.le_add_right n 1)).op ≫ ModuleCat.ofHom (tr n e).toLinearMap)
    (hepi : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n),
      Epi ((Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)).map f))
    (hAA : Functor.DescendsIsos (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ))
      (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)))
    (hML : (selfIsomSystem Λ Mt tr).IsMittagLeffler) :
    (Functor.isoTower (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ))
      (Mt ⋙ constantSheaf J (ModuleCat.{max u v x} Λ)) hepi hAA).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective_natTrans
    (isoTowerComparison J Λ Mt tr hfp hT htr hepi hAA)
    (fun i => (bijective_isoTowerComparisonApp J Λ Mt hfp hT i.unop).surjective)
    (hML.comp_type (constantGlobalSections.{u, v, x} J (T := T)))

end Tower

end Stacks.ConstantSheaf

end
