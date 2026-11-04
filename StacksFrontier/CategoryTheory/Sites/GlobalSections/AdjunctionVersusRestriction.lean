module

public import Mathlib.CategoryTheory.Sites.GlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adjoint and the limit descriptions of global sections agree on restrictions

`CategoryTheory.Sheaf.Γ` is defined as the right adjoint of the constant sheaf functor, and it is
*also* a limit of the underlying presheaf (`CategoryTheory.Sheaf.isLimitConeΓ`), the cone
projections being the restriction maps `CategoryTheory.Sheaf.ΓRes`. Mathlib relates the two
descriptions nowhere: `CategoryTheory.Sheaf.ΓHomEquiv` and
`CategoryTheory.Sheaf.ΓObjEquivHom` come with naturality in the sheaf and in the object, and
`ΓRes` with naturality in the sheaf, but no lemma says what the natural transformation
corresponding to a map into global sections does at an object.

That is what this file supplies: the component at `U` of `ΓHomEquiv.symm s` is `s` followed by
restriction to `U`.

## Main results

* `CategoryTheory.Sheaf.ΓHomEquiv_symm_app`.
* `CategoryTheory.Sheaf.constantSheafΓAdj_homEquiv_symm_app` — the same with the sheafification
  and the constant-sheaf adjunctions separated.
* `CategoryTheory.Sheaf.unique_sections_of_isTerminal` and
  `CategoryTheory.Sheaf.subsingleton_sections_of_isTerminal` — a terminal sheaf of types has
  exactly one section over every object.
* `CategoryTheory.Sheaf.sheafificationAdjunction_homEquiv_ΓObjEquivHom_app_apply` — the same
  bridge for `CategoryTheory.Sheaf.ΓObjEquivHom`, read on elements.
* `CategoryTheory.Sheaf.ΓObjEquivHom_hom_app_apply` — the same with the section of the constant
  sheaf quantified over rather than named, which is what a consumer composing two such bridges
  across two sites needs.

## Implementation notes

The proof is one application of `CategoryTheory.Sheaf.ΓHomEquiv_naturality_left_symm`:
`CategoryTheory.Sheaf.coneΓ` is by definition the cone whose projection family is
`ΓHomEquiv.symm (𝟙 _)`, so writing `s` as `s ≫ 𝟙` moves `s` out through the equivalence and
leaves exactly that family.

This is the first step of the comparison that identifies the global sections of a direct image
along a morphism of sites with the global sections upstairs
(`Stacks.ConstantSheaf.gammaPushforwardEquiv`) *as restriction-compatible* maps: that equivalence
is built from `ΓObjEquivHom` and the inverse-image adjunction, and relating it to `ΓRes` is
impossible without a bridge between the adjoint and the limit descriptions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v₂ u₂

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u₂} [Category.{v₂} A] [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]

/-- **A map into global sections, read as a map of presheaves, restricts to itself.** For
`s : X ⟶ Γ(F)`, the natural transformation from the constant presheaf on `X` that `s` corresponds
to under `CategoryTheory.Sheaf.ΓHomEquiv` has component at `U` equal to `s` followed by the
restriction map to `U`.

This is the bridge between the two descriptions of `CategoryTheory.Sheaf.Γ` — right adjoint of the
constant sheaf functor, and limit of the underlying presheaf — which Mathlib defines both of and
never compares. -/
lemma ΓHomEquiv_symm_app {X : A} {F : Sheaf J A} (s : X ⟶ (Γ J A).obj F) (U : Cᵒᵖ) :
    (ΓHomEquiv.symm s).app U = s ≫ F.ΓRes U := by
  conv_lhs => rw [← Category.comp_id s]
  rw [ΓHomEquiv_naturality_left_symm]
  simp only [NatTrans.comp_app, Functor.const_map_app]
  rfl

/-- **The same statement with the two adjunctions separated, which is the form a consumer of the
constant-sheaf adjunction has it in.** `CategoryTheory.Sheaf.ΓHomEquiv` is by definition the
composite of the sheafification adjunction with the constant-sheaf/global-sections adjunction, so
splitting it costs nothing; what the split buys is that the *sheaf* morphism
`(constantSheaf J A).obj X ⟶ F` corresponding to `s` appears explicitly, and that is what
`CategoryTheory.Sheaf.ΓObjEquivHom` produces and what every comparison built from the
inverse-image adjunction manipulates.

The sheafification half stays in `CategoryTheory.Adjunction.homEquiv` form: no
`CategoryTheory.GrothendieckTopology.toSheafify` appears, so a consumer continues with that
adjunction's own naturality rather than with the sheafification unit. -/
lemma constantSheafΓAdj_homEquiv_symm_app {X : A} {F : Sheaf J A}
    (s : X ⟶ (Γ J A).obj F) (U : Cᵒᵖ) :
    ((sheafificationAdjunction J A).homEquiv ((Functor.const Cᵒᵖ).obj X) F
        (((constantSheafΓAdj J A).homEquiv X F).symm s)).app U = s ≫ F.ΓRes U :=
  ΓHomEquiv_symm_app s U

/-! ### Sections of a terminal sheaf of types

The collapse of the comparison at a morphism of sites rests on this: the sheaves that appear in
`Stacks.ConstantSheaf.gammaPushforwardEquiv` between the global sections and the sheaf itself are
constant sheaves at a singleton, which are *terminal*, and a map into a terminal sheaf's sections
is forced. So the unit of the inverse-image adjunction
(`CategoryTheory.Sheaf.rightAdjunct_hom_app`) and the component of
`Stacks.ConstantSheaf.inverseImageTerminalIso` never have to be computed: whatever they are, they
land in a singleton.
-/

/-- **A terminal sheaf of types has exactly one section over every object.**

`CategoryTheory.sheafToPresheaf` creates, hence preserves, limits, so the underlying presheaf of a
terminal sheaf is a terminal presheaf; limits in a functor category are computed pointwise, so
evaluation at an object preserves them too; and a terminal object of `Type w` is a singleton by
`CategoryTheory.Limits.Types.isTerminalEquivUnique`.

No sheafification and no global sections functor are needed: the statement is about the sheaf
category's terminal object alone. -/
@[instance_reducible, sga "4 IV 6.4.3" "special case", sga "4 VI 7.4.13.5" "special case"]
noncomputable def unique_sections_of_isTerminal {T : Sheaf J (Type w)} (hT : IsTerminal T)
    (U : Cᵒᵖ) :
    Unique (T.obj.obj U) :=
  Types.isTerminalEquivUnique _
    (IsTerminal.isTerminalObj ((evaluation Cᵒᵖ (Type w)).obj U) T.obj
      (IsTerminal.isTerminalObj (sheafToPresheaf J (Type w)) T hT))

/-- **A terminal sheaf of types has a subsingleton of sections over every object.** The half of
`unique_sections_of_isTerminal` that a forcing argument uses: two maps into those sections agree
without either being computed. -/
lemma subsingleton_sections_of_isTerminal {T : Sheaf J (Type w)} (hT : IsTerminal T) (U : Cᵒᵖ) :
    Subsingleton (T.obj.obj U) :=
  have := unique_sections_of_isTerminal hT U
  inferInstance

/-- **A global section of a sheaf of types, read as a morphism out of the constant sheaf,
restricts to itself.** `CategoryTheory.Sheaf.ΓObjEquivHom` turns a global section `x` of `F` into
a morphism of sheaves `X_J ⟶ F` out of the constant sheaf on a one-element type; pushing that
morphism back to presheaves along the sheafification adjunction and evaluating at `U` gives a map
`X ⟶ F(U)`, and this says its value at the unique element of `X` is the restriction of `x` to `U`.

This is `constantSheafΓAdj_homEquiv_symm_app` with the map `X ⟶ Γ(F)` taken to be the constant
map at `x`, which is exactly what `ΓObjEquivHom` feeds to the constant-sheaf adjunction, read on
elements. It is the form a comparison of global sections built from `ΓObjEquivHom` needs in order
to say anything about `CategoryTheory.Sheaf.ΓRes`: the sheafification half is left in
`CategoryTheory.Adjunction.homEquiv` form for the same reason as there, so no
`CategoryTheory.GrothendieckTopology.toSheafify` appears. -/
lemma sheafificationAdjunction_homEquiv_ΓObjEquivHom_app_apply [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {X : Type w} [Unique X] {F : Sheaf J (Type w)}
    (x : (Γ J (Type w)).obj F) (U : Cᵒᵖ) :
    ((sheafificationAdjunction J (Type w)).homEquiv ((Functor.const Cᵒᵖ).obj X) F
        (ΓObjEquivHom J F X x)).app U (default : X) = F.ΓRes U x := by
  rw [show ΓObjEquivHom J F X x =
    ((constantSheafΓAdj J (Type w)).homEquiv X F).symm
      (TypeCat.homEquiv.symm fun _ => x) from rfl, constantSheafΓAdj_homEquiv_symm_app]
  rfl

/-- **The morphism out of the constant sheaf that a global section corresponds to takes every
section of the constant sheaf to the restriction of that global section.** For `x : Γ(F)`, the
morphism `X_J ⟶ F` of `CategoryTheory.Sheaf.ΓObjEquivHom` sends *any* section of `X_J` over `U` to
`F.ΓRes U x`, provided the sections of `X_J` over `U` form a subsingleton — which they do whenever
`X_J` is a terminal sheaf, by `unique_sections_of_isTerminal`.

This is the form in which a comparison of global sections built from `ΓObjEquivHom` is usable, and
the subsingleton is what makes it so. The statement that names the section instead —
`sheafificationAdjunction_homEquiv_ΓObjEquivHom_app_apply`, where it is the one the sheafification
unit produces — cannot be composed across two sites: naming it forces the spelling
`(presheafToSheaf J A).obj ((Functor.const _).obj X)` alongside `(constantSheaf J A).obj X`, the
two are only definitionally equal, and a goal carrying both is ill-typed at `implicit`
transparency, so every rewrite into it is refused.

The proof is `CategoryTheory.Sheaf.ΓRes_naturality` at that morphism, evaluated at the global
section of `X_J` corresponding to the identity: by
`CategoryTheory.Sheaf.ΓObjEquivHom_naturality_symm` the functor `Sheaf.Γ` carries that section to
`x`. So no description of `Sheaf.Γ` beyond its naturality is used. -/
lemma ΓObjEquivHom_hom_app_apply [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {X : Type w} [Unique X] {F : Sheaf J (Type w)}
    (x : (Γ J (Type w)).obj F) (U : Cᵒᵖ)
    [Subsingleton (((constantSheaf J (Type w)).obj X).obj.obj U)]
    (p : ((constantSheaf J (Type w)).obj X).obj.obj U) :
    (ΓObjEquivHom J F X x).hom.app U p = F.ΓRes U x := by
  have hx : (Γ J (Type w)).map (ΓObjEquivHom J F X x)
      ((ΓObjEquivHom J ((constantSheaf J (Type w)).obj X) X).symm (𝟙 _)) = x := by
    rw [← ΓObjEquivHom_naturality_symm, Category.id_comp, Equiv.symm_apply_apply]
  have h := ConcreteCategory.congr_hom (ΓRes_naturality (ΓObjEquivHom J F X x) U)
    ((ΓObjEquivHom J ((constantSheaf J (Type w)).obj X) X).symm (𝟙 _))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx] at h
  rw [h]
  congr 1
  exact Subsingleton.elim _ _

end CategoryTheory.Sheaf

end
