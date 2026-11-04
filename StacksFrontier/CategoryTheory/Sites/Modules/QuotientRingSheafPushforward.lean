module

public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafRecognition

/-!
# A quotient of a sheaf of rings pushed forward along a functor of sites

Let `G : Cs ⥤ Ct` be a continuous and cocontinuous functor of sites, let `O` be a sheaf of
commutative rings on the target site and let `I ⊆ O` be a sheaf of ideals. Pushing forward along
`G` and forming the quotient are two operations on `O`, and this file compares their two orders:
the pushforward `G_* (O/I)` of the quotient is the quotient of `G_* O` by the sheaf of ideals of
`G_* O` whose sections over `W` are the sections of `I` over `G W`.

The comparison is not formal — a quotient is a sheafification, and the pushforward of a
sheafification is not a sheafification of anything — but it is immediate from the recognition of
a quotient by its kernel, `Stacks.Sites.quotientRingSheafIso`: the pushed-forward quotient map is
still locally surjective, `G` being cocontinuous, and its kernel over `W` is the kernel of the
original quotient map over `G W`, which is the ideal of sections of `I` there.

## Main definitions

* `Stacks.Sites.pushforwardToQuotientRingSheaf`: the quotient map `O ⟶ O/I` pushed forward.
* `Stacks.Sites.pushforwardKerIdeal`: the sheaf of ideals of `G_* O` it kills, namely the kernel
  ideal of the pushed-forward quotient map.
* `Stacks.Sites.pushforwardQuotientRingIso`: **the comparison** — for any sheaf of ideals of
  `G_* O` whose sections over `W` are the sections of `I` over `G W`, the quotient of `G_* O` by
  it is `G_* (O/I)`.

## Main results

* `Stacks.Sites.ker_toQuotientRingSheaf_app`: the kernel of the quotient map `O ⟶ O/I` over an
  object of the site is the ideal of sections of `I` there. This is the objectwise reading of
  `Stacks.Sites.kerIdeal_quotientRingHom`; it is *not* the objectwise statement
  `Stacks.Sites.ker_toQuotientPresheaf_app`, which is about the unsheafified quotient.
* `Stacks.Sites.isLocallySurjective_pushforwardToQuotientRingSheaf`: the pushed-forward quotient
  map is locally surjective.
* `Stacks.Sites.sectionIdeal_pushforwardKerIdeal`: the sections of `pushforwardKerIdeal` over `W`
  are the sections of `I` over `G W`, so the hypothesis of the comparison is satisfiable and the
  comparison is not vacuous.

## Implementation notes

**The ideal downstairs is an argument, with a sectionwise hypothesis, and that is the content and
not a weakening.** Two different sheaves of ideals of `G_* O` have different quotients, so a
consumer holding a quotient formed downstairs — by an ideal generated downstairs, say — can only
be told that it agrees with `G_* (O/I)` once its ideal is known to agree with the pushforward of
`I`, and the agreement has to be stated somehow. Sections over an object is the weakest form in
which it can be stated and the only form a consumer can check, the two ideals being submodules of
sheaves on different sites. `Stacks.Sites.pushforwardKerIdeal` is the canonical ideal satisfying
it.

**Why the kernel ideal rather than a pushforward of the sheaf of ideals.** A sheaf of ideals is a
`SheafOfModules.Submodule`, whose defining datum includes the locality of membership, so pushing
one forward would mean reproving locality across `G`. The kernel ideal of a morphism of sheaves
of rings is already a sheaf of ideals, `SheafOfModules.kerIdeal`, and the pushed-forward quotient
map has one; its sections are computed by `SheafOfModules.kerIdeal_obj`, so no locality is
reproved.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites


section Objectwise

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}]

/-- **The kernel of the quotient map `O ⟶ O/I` over an object of the site is the ideal of
sections of `I` there.** This is the objectwise reading of `Stacks.Sites.kerIdeal_quotientRingHom`
— the sheaf-level kernel being `I` on the nose — and not of
`Stacks.Sites.ker_toQuotientPresheaf_app`, which is about the *unsheafified* quotient and would
give only the inclusion in the ideal of sections after sheafification. -/
theorem ker_toQuotientRingSheaf_app (I : IdealSubsheaf O) (V : Cᵒᵖ) :
    RingHom.ker ((toQuotientRingSheaf I).hom.app V).hom = sectionIdeal I V :=
  SetLike.ext fun a =>
    Iff.trans (SheafOfModules.mem_kerIdeal (quotientRingHom I) V a).symm
      (SetLike.ext_iff.1 (congrArg (fun N : IdealSubsheaf O => N.obj V)
        (kerIdeal_quotientRingHom I)) a)

end Objectwise

section Pushforward

variable {Cs : Type u} [Category.{u} Cs] {Ct : Type u} [Category.{u} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt] [G.IsCocontinuous Js Jt]
  [Js.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Jt.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify Js CommRingCat.{u}] [HasWeakSheafify Jt CommRingCat.{u}]
  {O : Sheaf Jt CommRingCat.{u}} (I : IdealSubsheaf O)

/-- Pushforward along `G` on sheaves of commutative rings. -/
abbrev commRingPushforward : Sheaf Jt CommRingCat.{u} ⥤ Sheaf Js CommRingCat.{u} :=
  G.sheafPushforwardContinuous CommRingCat.{u} Js Jt

/-- **The quotient map `O ⟶ O/I` pushed forward along `G`**, a morphism of sheaves of
commutative rings on the source site. -/
abbrev pushforwardToQuotientRingSheaf :
    (commRingPushforward Js G).obj O ⟶ (commRingPushforward Js G).obj (quotientRingSheaf I) :=
  (commRingPushforward Js G).map (toQuotientRingSheaf I)

/-- **The pushed-forward quotient map is locally surjective**, `G` being cocontinuous. -/
instance isLocallySurjective_pushforwardToQuotientRingSheaf :
    Presheaf.IsLocallySurjective Js (pushforwardToQuotientRingSheaf Js G I).hom :=
  haveI := isLocallySurjective_toQuotientRingSheaf I
  Presheaf.isLocallySurjective_whisker Js Jt G (toQuotientRingSheaf I).hom

omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [HasWeakSheafify Js CommRingCat] in
/-- The kernel of the pushed-forward quotient map over an object `W` of the source site is the
ideal of sections of `I` over `G W`: the sections of a pushforward over `W` are the sections over
`G W`, and `Stacks.Sites.ker_toQuotientRingSheaf_app` computes the kernel there. -/
theorem ker_pushforwardToQuotientRingSheaf_app (V : Csᵒᵖ) :
    RingHom.ker ((pushforwardToQuotientRingSheaf Js G I).hom.app V).hom =
      sectionIdeal I (op (G.obj V.unop)) :=
  ker_toQuotientRingSheaf_app I (op (G.obj V.unop))

/-- **The sheaf of ideals of `G_* O` that the pushed-forward quotient map kills**: its kernel
ideal. -/
abbrev pushforwardKerIdeal : IdealSubsheaf ((commRingPushforward Js G).obj O) :=
  SheafOfModules.kerIdeal ((sheafCompose Js (forget₂ CommRingCat.{u} RingCat.{u})).map
    (pushforwardToQuotientRingSheaf Js G I))

omit [G.IsCocontinuous Js Jt] [HasWeakSheafify Js CommRingCat] in
/-- **The sections of `Stacks.Sites.pushforwardKerIdeal` over `W` are the sections of `I` over
`G W`.** So the hypothesis of the comparison below is satisfiable, and the comparison is not
vacuous. -/
theorem sectionIdeal_pushforwardKerIdeal (V : Csᵒᵖ) :
    sectionIdeal (pushforwardKerIdeal Js G I) V = sectionIdeal I (op (G.obj V.unop)) :=
  (SheafOfModules.kerIdeal_obj _ V).trans (ker_pushforwardToQuotientRingSheaf_app Js G I V)

/-- **The pushforward of a quotient is the quotient by the pushed-forward ideal.** Let `I'` be a
sheaf of ideals of `G_* O` whose sections over every object `W` of the source site are the
sections of `I` over `G W`. Then the quotient of `G_* O` by `I'`, formed on the source site, is
the pushforward of the quotient `O/I`, compatibly with the two quotient maps
(`Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafIso_hom`).

This is `Stacks.Sites.quotientRingSheafIso` applied to the pushed-forward quotient map, which is
locally surjective because `G` is cocontinuous and whose kernel is `I'` by hypothesis. -/
def pushforwardQuotientRingIso (I' : IdealSubsheaf ((commRingPushforward Js G).obj O))
    (hI' : ∀ V : Csᵒᵖ, sectionIdeal I' V = sectionIdeal I (op (G.obj V.unop))) :
    quotientRingSheaf I' ≅ (commRingPushforward Js G).obj (quotientRingSheaf I) :=
  quotientRingSheafIso (pushforwardToQuotientRingSheaf Js G I) I' fun V =>
    (ker_pushforwardToQuotientRingSheaf_app Js G I V).trans (hI' V).symm

/-- **The pushforward of a quotient is the quotient by its own kernel ideal**, the hypothesis-free
instance of `Stacks.Sites.pushforwardQuotientRingIso`. -/
def pushforwardQuotientRingIsoKer :
    quotientRingSheaf (pushforwardKerIdeal Js G I) ≅
      (commRingPushforward Js G).obj (quotientRingSheaf I) :=
  pushforwardQuotientRingIso Js G I _ (sectionIdeal_pushforwardKerIdeal Js G I)

end Pushforward

end Stacks.Sites

end
