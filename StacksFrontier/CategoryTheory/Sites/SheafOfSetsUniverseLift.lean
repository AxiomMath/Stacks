module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.UliftFunctorSheafification

/-!
# Enlarging the universe of a sheaf of sets

A site `C : Type u` with `Category.{v} C` has a smallest universe of sets in which its sheaves
carry a Yoneda lemma, namely `max u v`: the sheafified representable
`CategoryTheory.Sheaf.sheafifiedYoneda` lands in `Sheaf J (Type max u v)` and in no larger
universe. Some statements about sheaves of modules force a strictly larger coefficient universe —
a ring `Λ : Type r` with modules in `ModuleCat.{max u v r} Λ`, the shape extension by zero and
Stacks 0960 are stated at — and then a sheaf of sets in `Type (max u v r)` is needed to compare
with. This file supplies it.

The sheafified representable at the larger universe is *not* a second spelling of
`CategoryTheory.Sheaf.sheafifiedYoneda`: at the smallest universe the two are the same
declaration unfolded, which `CategoryTheory.Sheaf.sheafifiedUliftYoneda_eq` records. Consumers
whose coefficient universe is `max u v` should use `CategoryTheory.Sheaf.sheafifiedYoneda`;
`CategoryTheory.Sheaf.sheafifiedUliftYoneda` exists for the statements whose coefficient universe
is larger, where the former does not typecheck. The two are identified by
`CategoryTheory.Sheaf.sheafifiedUliftYonedaIsoSheafCompose`, so a property of `h_U^#` proved at
`max u v` is transported rather than reproved.

## Main definitions

* `CategoryTheory.Sheaf.sheafifiedUliftYoneda`: the functor `U ↦ h_U^#` with values in
  `Sheaf J (Type max u v s)` for an arbitrary further universe `s`.
* `CategoryTheory.Sheaf.uliftSectionEquiv`: its Yoneda lemma for sheaves,
  `Mor(h_X^#, F) ≃ F(X)`.

## Main results

* `CategoryTheory.Sheaf.sheafifiedUliftYonedaIsoSheafCompose`: the sheafified representable at the
  larger universe is the pointwise universe lift of the sheafified representable at `max u v`.
* `Stacks.Sites.sheafPullbackSheafifiedUliftYonedaIso`: **Stacks 04D3 for sheafified
  representables** at the larger universe — inverse image along a continuous functor of sites
  carries `h_U^#` to `h_{π U}^#`.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor`: finite local constancy
  survives the pointwise universe lift of a sheaf of sets.

## Implementation notes

`CategoryTheory.Sheaf.sheafifiedYoneda` itself cannot be given the extra universe parameter: it
would occur only in the result type, nothing would determine it, and already inside its own file
Lean reports `stuck at solving universe constraint max u v ?s =?= max u v s`. The parallel
definition is therefore the only available shape, and the reason the bridge isomorphism is
provided rather than left to the reader.

The bridge is `CategoryTheory.sheafComposeNatIso` for `CategoryTheory.uliftFunctor`, which both
admits sheaf composition and preserves sheafification, composed with the identification of
`uliftYoneda.{max u s}` with `uliftYoneda.{u}` followed by a further universe lift — the two
being `yoneda` followed by one and by two applications of `CategoryTheory.uliftFunctor`.

The transport of finite local constancy needs the universe lift to commute with the constant
sheaf, which is Mathlib's `CategoryTheory.constantCommuteCompose`, and with restriction to
a localized site, which holds definitionally: both are whiskerings, on the left by
`(Over.forget V).op` and on the right by `CategoryTheory.uliftFunctor`. It does *not* need the
universe lift to commute with inverse image along a continuous functor of sites, which is why no
Kan extension appears here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe s w v u

namespace CategoryTheory

/-- Lifting the universe of a type in two steps is lifting it in one, in the shape the
sheafified representable needs: the second lift absorbs the universe of the site.

`CategoryTheory.uliftFunctorCompIso` in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology` is the same statement with the two
lift levels free, and subsumes this one; it is not used here because that module is a cohomology
module and importing it would pull the whole of sheaf cohomology into a basic site file. The two
should be merged once that definition moves to a module below this one. -/
public def uliftFunctorMaxCompIso :
    uliftFunctor.{u, v} ⋙ uliftFunctor.{max u v s, max u v} ≅ uliftFunctor.{max u s, v} :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso ((Equiv.ulift.trans Equiv.ulift).trans Equiv.ulift.symm))
    (fun _ => rfl)

namespace Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The identification of `uliftYoneda` at a composite universe with `uliftYoneda` at the
universe of the site followed by a further universe lift. -/
public def uliftYonedaCompUliftFunctorIso :
    uliftYoneda.{u, v, u} (C := C) ⋙
        (Functor.whiskeringRight Cᵒᵖ (Type max u v) (Type max u v s)).obj
          uliftFunctor.{max u v s, max u v} ≅
      uliftYoneda.{max u s, v, u} (C := C) :=
  Functor.isoWhiskerLeft yoneda
    ((Functor.whiskeringRight _ _ _).mapIso uliftFunctorMaxCompIso.{s, v, u})

section Yoneda

variable [HasWeakSheafify J (Type max u v s)]

/-- The sheafified Yoneda embedding `U ↦ h_U^#` into sheaves of sets in a universe `max u v s`
larger than the universe `max u v` of `CategoryTheory.Sheaf.sheafifiedYoneda`.

At `s = u` this is `CategoryTheory.Sheaf.sheafifiedYoneda`, by
`CategoryTheory.Sheaf.sheafifiedUliftYoneda_eq`; it exists for the statements whose coefficient
universe is strictly larger, where that functor does not typecheck. -/
public def sheafifiedUliftYoneda : C ⥤ Sheaf J (Type max u v s) :=
  uliftYoneda.{max u s} ⋙ presheafToSheaf J (Type max u v s)

omit [HasWeakSheafify J (Type max u v s)] in
/-- At the universe of `CategoryTheory.Sheaf.sheafifiedYoneda` the two sheafified Yoneda
embeddings are the same declaration unfolded. -/
public theorem sheafifiedUliftYoneda_eq [HasWeakSheafify J (Type max u v)] :
    sheafifiedUliftYoneda.{u} J = sheafifiedYoneda J := rfl

/-- **Yoneda's lemma for sheaves of sets in a larger universe**: a morphism `h_X^# ⟶ F` out of a
sheafified representable is the same thing as a section of `F` over `X`. -/
public def uliftSectionEquiv {X : C} {F : Sheaf J (Type max u v s)} :
    ((sheafifiedUliftYoneda.{s} J).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction J (Type max u v s)).homEquiv
      (uliftYoneda.{max u s}.obj X) F).trans uliftYonedaEquiv.{max u s}

/-- Composing `α : h_X^# ⟶ F` with `β : F ⟶ G` acts on the corresponding sections by `β`. -/
public theorem uliftSectionEquiv_comp {X : C} {F G : Sheaf J (Type max u v s)}
    (α : (sheafifiedUliftYoneda.{s} J).obj X ⟶ F) (β : F ⟶ G) :
    uliftSectionEquiv J (α ≫ β) = β.hom.app (op X) (uliftSectionEquiv J α) :=
  congrArg (fun γ => uliftYonedaEquiv.{max u s} γ)
    ((sheafificationAdjunction J (Type max u v s)).homEquiv_naturality_right α β)

/-- **The sheafified representable at a larger universe is the universe lift of the sheafified
representable.** So every property of `h_U^#` proved at the universe `max u v` of the site may be
transported to the larger universe rather than reproved there. -/
public def sheafifiedUliftYonedaIsoSheafCompose [HasWeakSheafify J (Type max u v)] (X : C) :
    (sheafifiedUliftYoneda.{s} J).obj X ≅
      (sheafCompose J uliftFunctor.{max u v s, max u v}).obj ((sheafifiedYoneda J).obj X) :=
  (presheafToSheaf J (Type max u v s)).mapIso
      ((uliftYonedaCompUliftFunctorIso.{s} (C := C)).app X).symm ≪≫
    (sheafComposeNatIso J uliftFunctor.{max u v s, max u v}
      (sheafificationAdjunction J (Type max u v))
      (sheafificationAdjunction J (Type max u v s))).app (uliftYoneda.{u}.obj X)

end Yoneda

end Sheaf

end CategoryTheory

namespace Stacks.Sites

open CategoryTheory

section PullbackRepresentable

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (π : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [π.IsContinuous J K] [HasWeakSheafify J (Type max u v s)]
  [HasWeakSheafify K (Type max u v s)]
  [(π.sheafPushforwardContinuous (Type max u v s) J K).IsRightAdjoint]

/-- Morphisms out of the sheaf pullback of a sheafified representable are the sections over the
image object, at a universe of sets larger than that of the site: the adjunction between
pullback and pushforward, followed by Yoneda's lemma for sheaves. -/
public def sheafPullbackSheafifiedUliftYonedaSectionEquiv (U : C)
    (G : Sheaf K (Type max u v s)) :
    ((π.sheafPullback (Type max u v s) J K).obj
        ((Sheaf.sheafifiedUliftYoneda.{s} J).obj U) ⟶ G) ≃
      G.obj.obj (Opposite.op (π.obj U)) :=
  ((π.sheafAdjunctionContinuous (Type max u v s) J K).homEquiv _ G).trans
    ((Sheaf.uliftSectionEquiv J).trans
      (Equiv.cast (Functor.sheafPushforwardContinuous_obj_obj_obj π (Type max u v s) J K G
        (Opposite.op U))))

omit [HasWeakSheafify K (Type max u v s)] in
/-- The corepresentability bijection of
`Stacks.Sites.sheafPullbackSheafifiedUliftYonedaSectionEquiv` is natural in the test sheaf. -/
public theorem sheafPullbackSheafifiedUliftYonedaSectionEquiv_comp (U : C)
    {G G' : Sheaf K (Type max u v s)} (α : G ⟶ G')
    (f : (π.sheafPullback (Type max u v s) J K).obj
      ((Sheaf.sheafifiedUliftYoneda.{s} J).obj U) ⟶ G) :
    sheafPullbackSheafifiedUliftYonedaSectionEquiv π J K U G' (f ≫ α) =
      α.hom.app (Opposite.op (π.obj U))
        (sheafPullbackSheafifiedUliftYonedaSectionEquiv π J K U G f) := by
  simp only [sheafPullbackSheafifiedUliftYonedaSectionEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Sheaf.uliftSectionEquiv_comp]
  rfl

/-- Both the sheaf pullback of `h_U^#` and `h_{π U}^#` corepresent the sections over `π U`,
naturally in the test sheaf. -/
public def sheafPullbackSheafifiedUliftYonedaCorepIso (U : C) :
    coyoneda.obj (Opposite.op ((π.sheafPullback (Type max u v s) J K).obj
        ((Sheaf.sheafifiedUliftYoneda.{s} J).obj U))) ≅
      coyoneda.obj (Opposite.op ((Sheaf.sheafifiedUliftYoneda.{s} K).obj (π.obj U))) :=
  NatIso.ofComponents
    (fun G => Equiv.toIso
      ((sheafPullbackSheafifiedUliftYonedaSectionEquiv π J K U G).trans
        (Sheaf.uliftSectionEquiv K).symm))
    (by
      intro G G' α
      ext f
      change (Sheaf.uliftSectionEquiv K).symm
          (sheafPullbackSheafifiedUliftYonedaSectionEquiv π J K U G' (f ≫ α)) =
        (Sheaf.uliftSectionEquiv K).symm
          (sheafPullbackSheafifiedUliftYonedaSectionEquiv π J K U G f) ≫ α
      apply (Sheaf.uliftSectionEquiv K).injective
      rw [Equiv.apply_symm_apply, sheafPullbackSheafifiedUliftYonedaSectionEquiv_comp,
        Sheaf.uliftSectionEquiv_comp, Equiv.apply_symm_apply])

/-- **Stacks 04D3 for sheafified representables, at a larger universe of sets.** The sheaf
pullback along a continuous functor `π` of the sheaf represented by `U` is the sheaf represented
by `π U`. -/
public def sheafPullbackSheafifiedUliftYonedaIso (U : C) :
    (π.sheafPullback (Type max u v s) J K).obj ((Sheaf.sheafifiedUliftYoneda.{s} J).obj U) ≅
      (Sheaf.sheafifiedUliftYoneda.{s} K).obj (π.obj U) :=
  ((Coyoneda.fullyFaithful (C := Sheaf K (Type max u v s))).preimageIso
    (sheafPullbackSheafifiedUliftYonedaCorepIso π J K U)).unop.symm

end PullbackRepresentable

end Stacks.Sites

namespace Stacks.ConstantSheaf

open CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Finite local constancy survives the pointwise universe lift of a sheaf of sets.** The same
trivializing covering serves, the constant value `E` being replaced by its universe lift, which
is finite because `E` is.

The universe lift commutes with the constant sheaf by
`CategoryTheory.constantCommuteCompose`, and with restriction to a localized site
definitionally, both being whiskerings. -/
public theorem isFiniteLocallyConstant_sheafCompose_uliftFunctor
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v)]
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v s)]
    (F : Sheaf J (Type max u v)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteLocallyConstant J
      ((sheafCompose J uliftFunctor.{max u v s, max u v}).obj F) := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : Finite E := hE
  refine ⟨ULift.{max u v s} E, inferInstance, ⟨?_⟩⟩
  exact ((constantCommuteCompose (J.over (V i))
      uliftFunctor.{max u v s, max u v}).app E).symm ≪≫
    (sheafCompose (J.over (V i)) uliftFunctor.{max u v s, max u v}).mapIso e

end Stacks.ConstantSheaf

end
