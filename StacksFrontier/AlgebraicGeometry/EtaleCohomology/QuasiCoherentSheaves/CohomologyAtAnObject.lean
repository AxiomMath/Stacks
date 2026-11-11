module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Cotangent.CohomologyPresheaf.BiggerSiteObjectwise

/-!
# Cohomology of a quasi-coherent module over an arbitrary object of the site

Let `S` be a scheme, `F` a quasi-coherent `𝒪_S`-module and `C` a site of schemes over `S` —
one of `(Sch/S)_τ` for `τ` among fppf, syntomic, smooth, étale and Zariski, or the small étale
site.  Theorem 03P2 compares the Zariski cohomology of `F` on `S` with the `τ`-cohomology of
the associated sheaf `F^a` of Proposition 03OG.  Its right-hand side is cohomology over the
object `S` of `C`, and `S` is a final object there, so those groups are the right derived
functors of the global sections functor; this is the first assertion of Remark 03P3, and
`cohomologyAtFinalObjectIso` below is its form over a final object of an arbitrary site.

The substance of the remark is its second assertion: the proof of Theorem 03P2 gives the
comparison not only at the final object but at **every** object `f : U ⟶ S` of the site,

`H^p(U, f^*F) = H^p_τ(U, F^a)`,

the left-hand side being Zariski cohomology on `U` of the pullback module and the right-hand
side the cohomology of `F^a` over the object `f` of `C`.  Over an arbitrary site,
`zariskiCohomologyIsoCohomologyAtObject` reduces it to the comparison at a final object.

## Where Remark 03P3 itself is proved

The two assertions of Remark 03P3 are proved, for the sites of the source, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSheaves.CohomologyAtAnObjectCollapse`:
`AlgebraicGeometry.bigOverAssociatedSheafGlobalCohomologyIso` and
`AlgebraicGeometry.smallEtaleAssociatedSheafGlobalCohomologyIso` (first assertion), and
`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAtObject` and
`AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAtObject` (second assertion), for
`𝒞 = (Sch/S)_τ` with all five `τ` and for `𝒞 = S_étale`.  Those carry `@[stacks 03P3]`.

This file works instead over an arbitrary small site `(C, K)` presented by a functor
`πC : C ⥤ Over S`, where no comparison with Zariski cohomology is available in general.  It
proves the passage from a comparison at the final object of a site `D` of schemes over `U`
(the input `hFinal` of `zariskiCohomologyIsoCohomologyAtObject`) to the comparison at the object
`f` of `C`.  It has two ingredients, and neither is formal:

* **the associated sheaf restricts to the associated sheaf of the pullback.**  Restricting the
  presheaf of Tag 03DS of `(S, F)` along the inclusion `u : D ⥤ C` of the schemes over `U` in
  the schemes over `S` gives the presheaf of Tag 03DS of `(U, f^*F)`.  This is
  `restrictedAssociatedPresheafIso`, built from
  `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`, and `restrictedAssociatedSheafIso` is its
  sheaf-level form.
* **cohomology over an object does not change under restriction to a smaller site that hits
  that object.**  This is Stacks 03YU(2) in the form
  `Stacks.Cohomology.BiggerSite.cohomologyObjIso`.

Composing the two identifies `H^p_τ(U, F^a)` — cohomology of `F^a` over the object `f` of the
site over `S` — with the cohomology of `(f^*F)^a` over the final object of the site over `U`,
which is where `hFinal` applies.

## Main definitions

* `restrictedAssociatedPresheafIso`: `(F^a)|_D ≅ (f^*F)^a` for the presheaves of Tag 03DS.
* `restrictedAssociatedSheafIso`: the same isomorphism between the sheaves.
* `cohomologyAtObjectIso`: `H^p_τ(U, F^a) ≅ H^p(D, (f^*F)^a)` over the final object of `D`.

## Main results

* `objAtFinalObjectIso`: the object `u t` of `C` reached by the final object `t` of `D` is the
  object `f : U ⟶ S`.  This is what makes the conclusion a statement about `f`.
* `cohomologyAtFinalObjectIso`: over a final object of an arbitrary site the cohomology of
  `F^a` is the right derived functor of global sections.
* `zariskiCohomologyIsoCohomologyAtObject`: `H^p(U, f^*F) ≅ H^p(U, F^a)` at an object
  `f : U ⟶ S` of an arbitrary site, from the comparison at the final object of the site over
  `U`.

## Implementation notes

The site is an arbitrary small site `(C, K)` presented by a functor `πC : C ⥤ Over S`, which
is how the associated sheaf `F^a` of Proposition 03OG is built in
`StacksFrontier/AlgebraicGeometry/Topologies/AssociatedModuleOnSite.lean`: its underlying abelian
presheaf is `Stacks.Sites.associatedPresheaf S F πC = πC.op ⋙ quasiCoherentPresheafFunctor S F`.
That declaration is stated only for a site whose objects live one universe above its morphisms,
which excludes the small sites that carry sheaf cohomology here, so the composite is written out
rather than invoked; it is the same functor.  The five topologies of the source are covered by
the arbitrary `K`, as is the small étale site.

The sheaf conditions for `F^a` on `(C, K)` and for `(f^*F)^a` on `(D, J)` — Proposition 03OG,
equivalently Tag 03DT — are hypotheses `hFa` and `hFaPullback`: no sheafification occurs, and
the sections over an object of either site are exactly the global sections of the corresponding
pullback of the module.

Cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H'` over an object of a site, and
`CategoryTheory.Sheaf.H` globally; the Zariski side is `Sheaf.H'` over `⊤` on the site of opens,
which is the spelling used throughout this repository for the cohomology of a module on a
scheme.  The two sides are not definitionally equal: the left-hand side is an `Ext`-group in
abelian sheaves on `U.Opens`, the right-hand side an `Ext`-group in abelian sheaves on `(C, K)`.

## References

* [Stacks Project, Tag 03P3](https://stacks.math.columbia.edu/tag/03P3)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03OG](https://stacks.math.columbia.edu/tag/03OG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.QcohSiteCohomology

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {S Y : Scheme.{u}}

/-! ### The associated presheaf restricts to the associated presheaf of the pullback -/

/-- **The associated presheaf of Proposition 03OG restricts to the associated presheaf of the
pullback.**  Let `u : D ⥤ C` be the inclusion of a site of schemes over `Y` into a site of
schemes over `S`, compatible through `e` with composing the structure morphisms with
`f : Y ⟶ S`.  Then restricting the presheaf of Tag 03DS of `(S, F)` along `u` gives the
presheaf of Tag 03DS of `(Y, f^*F)`.

This is `Stacks.Sites.quasiCoherentPresheafBaseChangeIso` at the object `Over.mk f`,
transported along `e`. -/
def restrictedAssociatedPresheafIso (f : Y ⟶ S) (F : S.Modules) [F.IsQuasicoherent]
    (πC : C ⥤ Over S) (πD : D ⥤ Over Y) (u : D ⥤ C) (e : u ⋙ πC ≅ πD ⋙ Over.map f) :
    u.op ⋙ (πC.op ⋙ quasiCoherentPresheafFunctor S F) ≅
      πD.op ⋙ quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback f).obj F) :=
  (Functor.associator u.op πC.op (quasiCoherentPresheafFunctor S F)).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op e).symm (quasiCoherentPresheafFunctor S F) ≪≫
      Functor.associator πD.op (Over.map f).op (quasiCoherentPresheafFunctor S F) ≪≫
        Functor.isoWhiskerLeft πD.op
          (Stacks.Sites.quasiCoherentPresheafBaseChangeIso F (Over.mk f))

/-- **The object of the site reached by the final object of the smaller site is `f`.**  If the
final object of the site `D` of schemes over `Y` is the identity of `Y`, then the object `u t`
of the site `C` of schemes over `S` is `f : Y ⟶ S`.  This is what makes
`zariskiCohomologyIsoCohomologyAtObject` a statement about an arbitrary object of `C` and not
about a final one. -/
def objAtFinalObjectIso (f : Y ⟶ S) (πC : C ⥤ Over S) (πD : D ⥤ Over Y) (u : D ⥤ C)
    (e : u ⋙ πC ≅ πD ⋙ Over.map f) (t : D) (ht : πD.obj t ≅ Over.mk (𝟙 Y)) :
    πC.obj (u.obj t) ≅ Over.mk f :=
  e.app t ≪≫ (Over.map f).mapIso ht ≪≫ Over.isoMk (Iso.refl Y) (by simp)

/-! ### The associated sheaf of Proposition 03OG -/

variable (f : Y ⟶ S) (F : S.Modules) [F.IsQuasicoherent]
  (πC : C ⥤ Over S) (πD : D ⥤ Over Y) (u : D ⥤ C)
  (J : GrothendieckTopology D) (K : GrothendieckTopology C)

/-- **The associated sheaf `F^a` of Proposition 03OG** on the site `(C, K)` of schemes over `S`:
the sheaf whose sections over an object `g : T ⟶ S` are the global sections of `g^*F`.  The
sheaf condition is the hypothesis `hFa`; no sheafification occurs. -/
def associatedSheaf (hFa : Presheaf.IsSheaf K (πC.op ⋙ quasiCoherentPresheafFunctor S F)) :
    Sheaf K AddCommGrpCat.{u} :=
  ⟨πC.op ⋙ quasiCoherentPresheafFunctor S F, hFa⟩

/-- **The associated sheaf `(f^*F)^a`** on the site `(D, J)` of schemes over `Y`. -/
def associatedSheafPullback (hFaPullback : Presheaf.IsSheaf J
    (πD.op ⋙ quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback f).obj F))) :
    Sheaf J AddCommGrpCat.{u} :=
  ⟨πD.op ⋙ quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback f).obj F), hFaPullback⟩

@[simp]
theorem associatedSheaf_obj
    (hFa : Presheaf.IsSheaf K (πC.op ⋙ quasiCoherentPresheafFunctor S F)) :
    (associatedSheaf F πC K hFa).obj = πC.op ⋙ quasiCoherentPresheafFunctor S F := rfl

@[simp]
theorem associatedSheafPullback_obj (hFaPullback : Presheaf.IsSheaf J
    (πD.op ⋙ quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback f).obj F))) :
    (associatedSheafPullback f F πD J hFaPullback).obj =
      πD.op ⋙ quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback f).obj F) := rfl

section Comparison

variable [u.IsContinuous J K] [u.IsCocontinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsRightAdjoint]
  [∀ P : Dᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasPointwiseRightKanExtension P]
  [(u.sheafPullback AddCommGrpCat.{u} J K).PreservesMonomorphisms]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  (hFa : Presheaf.IsSheaf K (πC.op ⋙ quasiCoherentPresheafFunctor S F))
  (hFaPullback : Presheaf.IsSheaf J
    (πD.op ⋙ quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback f).obj F)))

/-- **`restrictedAssociatedPresheafIso` between the sheaves.**  The restriction of `F^a` to the
site of schemes over `Y` is `(f^*F)^a`.  Restriction is written as the sheaf pullback along the
cocontinuous `u`, which is the functor
`Stacks.Cohomology.BiggerSite.cohomologyObjIso` compares cohomology along. -/
def restrictedAssociatedSheafIso (e : u ⋙ πC ≅ πD ⋙ Over.map f) :
    (u.sheafPullbackCocontinuous AddCommGrpCat.{u} J K).obj (associatedSheaf F πC K hFa) ≅
      associatedSheafPullback f F πD J hFaPullback :=
  (u.sheafPullbackCocontinuousIsoSheafPushforwardContinuous AddCommGrpCat.{u} J K).app
      (associatedSheaf F πC K hFa) ≪≫
    (sheafToPresheaf J AddCommGrpCat.{u}).preimageIso
      (restrictedAssociatedPresheafIso f F πC πD u e)

/-- **The comparison of Remark 03P3 on the site side.**  The `τ`-cohomology of `F^a` over the
object `u t` of the site of schemes over `S` is the cohomology of `(f^*F)^a` over the object `t`
of the site of schemes over `Y`.

Two things go into this: cohomology over an object does not change under restriction along a
continuous and cocontinuous functor hitting that object (Stacks 03YU(2),
`Stacks.Cohomology.BiggerSite.cohomologyObjIso`), and the restriction of `F^a` is `(f^*F)^a`
(`restrictedAssociatedSheafIso`). -/
def cohomologyAtObjectIso (e : u ⋙ πC ≅ πD ⋙ Over.map f) (p : ℕ) (t : D) :
    Sheaf.H' (associatedSheaf F πC K hFa) p (u.obj t) ≅
      Sheaf.H' (associatedSheafPullback f F πD J hFaPullback) p t :=
  Stacks.Cohomology.BiggerSite.cohomologyObjIso J K u
      (associatedSheaf F πC K hFa) p t ≪≫
    (Sheaf.cohomologyPresheafFunctor J p ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op t)).mapIso
      (restrictedAssociatedSheafIso f F πC πD u J K hFa hFaPullback e)

/-! ### Remark 03P3 -/

/-- **Cohomology of `F^a` over a final object is derived global sections**, on an arbitrary
site `C` of schemes over `S`: over a final object `T` of `C` the groups `H^p(T, F^a)` are the
right derived functors of the global sections functor of the site, that is Mathlib's global
`CategoryTheory.Sheaf.H`.

For the sites of [Stacks, Tag 03P3] this is
`AlgebraicGeometry.bigOverAssociatedSheafGlobalCohomologyIso` and
`AlgebraicGeometry.smallEtaleAssociatedSheafGlobalCohomologyIso`. -/
def cohomologyAtFinalObjectIso (p : ℕ) (T : C) (hT : IsTerminal T) :
    Sheaf.H' (associatedSheaf F πC K hFa) p T ≅
      AddCommGrpCat.of (Sheaf.H (associatedSheaf F πC K hFa) p) :=
  Stacks.Cohomology.TerminalCohomology.h'IsoH K (associatedSheaf F πC K hFa) p T hT

/-- **From the final object to an arbitrary object**, on an arbitrary site `C` of schemes over
`S`: given, for the scheme `Y`, the module `f^*F` and the final object `t` of a site `D` of
schemes over `Y`, an isomorphism `hFinal : H^p(Y, f^*F) ≅ H^p(t, (f^*F)^a)`, one gets

`H^p(Y, f^*F) ≅ H^p(Y, F^a)`

over the object `u t` of `C`, which `objAtFinalObjectIso` identifies with `f : Y ⟶ S`.
`cohomologyAtObjectIso` moves the right-hand side of `hFinal` from `t` to `u t`.

For the sites of [Stacks, Tag 03P3] the statement is proved outright, with no input, as
`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAtObject` and
`AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAtObject`. -/
def zariskiCohomologyIsoCohomologyAtObject (e : u ⋙ πC ≅ πD ⋙ Over.map f) (p : ℕ) (t : D)
    (hFinal :
      Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
          ((Scheme.Modules.pullback f).obj F)) p (⊤ : Y.Opens) ≅
        Sheaf.H' (associatedSheafPullback f F πD J hFaPullback) p t) :
    Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pullback f).obj F)) p (⊤ : Y.Opens) ≅
      Sheaf.H' (associatedSheaf F πC K hFa) p (u.obj t) :=
  hFinal ≪≫ (cohomologyAtObjectIso f F πC πD u J K hFa hFaPullback e p t).symm

end Comparison

end Stacks.EtaleCohomology.QcohSiteCohomology

end
