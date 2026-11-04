module

public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriek
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomAdjunction

/-!
# `SheafHom(h_U^#, F) = j_{U*}(F|_{C/U})`

Let `(C, J)` be a small site and `U` an object of `C`. Stacks 0D7X asserts
`SheafHom(h_U^\#, \mathcal{F}) = j_{U*}(\mathcal{F}|_{\mathcal{C}/U})` for a sheaf of sets
`\mathcal{F}` on `C`, where `SheafHom` is the internal hom sheaf
`V \mapsto Mor_{Sh(C/V)}(-|_{C/V}, -|_{C/V})` (Mathlib's `CategoryTheory.sheafHom`).

## Implementation

The source's proof is the chain of natural bijections
`Mor(\mathcal{G}, j_{U*}(\mathcal{F}|_{C/U})) = Mor(\mathcal{G}|_{C/U}, \mathcal{F}|_{C/U})
= Mor(j_{U!}(\mathcal{G}|_{C/U}), \mathcal{F}) = Mor(\mathcal{G} \times h_U^\#, \mathcal{F})
= Mor(\mathcal{G}, SheafHom(h_U^\#, \mathcal{F}))`, concluded by Yoneda; the third step is
Stacks 03EE and the fourth is Stacks 0BWQ.

Here that chain is packaged as two adjunctions with the same left adjoint
`\mathcal{G} \mapsto h_U^\# \times \mathcal{G}`:

* `CategoryTheory.OverShriek.prodOverPullbackOverPushforwardAdjunction`, whose right adjoint is
  `j_{U*} \circ j_U^{-1}` — this is the first three bijections, i.e. the two localization
  adjunctions `j_{U!} \dashv j_U^{-1} \dashv j_{U*}` together with Stacks 03EE made natural
  (`overShriekOverPullbackNatIso`);
* `CategoryTheory.SheafHomAdj.prodSheafHomAdjunction`, whose right adjoint is `SheafHom(h_U^\#, -)`
  — this is Stacks 0BWQ read with Stacks' own `SheafHom`.

Uniqueness of right adjoints (`Adjunction.rightAdjointUniq`) is then exactly the Yoneda step of the
source, and it delivers the isomorphism naturally in `F`, which is more than the tag asks for.

## Main results

* `CategoryTheory.OverShriek.sheafHomYonedaSheafifyNatIso`: **Stacks 0D7X**, as an isomorphism of
  functors `Sh(C) ⥤ Sh(C)`.
* `CategoryTheory.OverShriek.sheafHomYonedaSheafifyIso`: its value at a single sheaf `F`, which is
  the displayed formula of the tag.

Tags covered: 0D7X.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u

namespace CategoryTheory.OverShriek

variable {C : Type u} [SmallCategory C] (U : C) (J : GrothendieckTopology C)

/-- **Stacks 0D7X.** For an object `U` of a small site `(C, J)`, the internal hom sheaf
`SheafHom(h_U^\#, -)` out of the sheafification of the representable presheaf `h_U` is the
composite `j_{U*} \circ j_U^{-1}`: that is,
`SheafHom(h_U^\#, \mathcal{F}) = j_{U*}(\mathcal{F}|_{\mathcal{C}/U})`, naturally in the sheaf
`\mathcal{F}`.

Both functors are right adjoint to `\mathcal{G} \mapsto h_U^\# \times \mathcal{G}`, the first by
Stacks 0BWQ and the second by the localization adjunctions together with Stacks 03EE, so they agree
by uniqueness of right adjoints. This is the source's argument, whose last step is the Yoneda
lemma. -/
@[stacks 0D7X]
noncomputable def sheafHomYonedaSheafifyNatIso :
    SheafHomAdj.sheafHomFunctor ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) ≅
      localizationPullback U J ⋙ localizationPushforward U J :=
  (Adjunction.rightAdjointUniq (prodOverPullbackOverPushforwardAdjunction U J)
    (SheafHomAdj.prodSheafHomAdjunction
      ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))).symm

/-- **Stacks 0D7X**, at a single sheaf: `SheafHom(h_U^\#, \mathcal{F}) \cong
j_{U*}(\mathcal{F}|_{\mathcal{C}/U})`. -/
noncomputable def sheafHomYonedaSheafifyIso (F : Sheaf J (Type u)) :
    sheafHom ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) F ≅
      (localizationPushforward U J).obj ((localizationPullback U J).obj F) :=
  (sheafHomYonedaSheafifyNatIso U J).app F

end CategoryTheory.OverShriek
