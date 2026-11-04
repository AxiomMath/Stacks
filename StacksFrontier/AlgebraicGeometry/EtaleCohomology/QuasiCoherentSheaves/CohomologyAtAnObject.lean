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
functors of the global sections functor; this is the first assertion of Remark 03P3 and is
`cohomologyAtFinalObjectIso` below.

The substance of the remark is its second assertion: the proof of Theorem 03P2 gives the
comparison not only at the final object but at **every** object `f : U ⟶ S` of the site,

`H^p(U, f^*F) = H^p_τ(U, F^a)`,

the left-hand side being Zariski cohomology on `U` of the pullback module and the right-hand
side the cohomology of `F^a` over the object `f` of `C`.  That is
`zariskiCohomologyIsoCohomologyAtObject`.

## The reduction this file carries out

Theorem 03P2 itself is **not** available in this repository, so it is carried as the explicit
named hypothesis `h03P2`: the comparison at the final object of a site `D` of schemes over `U`.
What is proved here is the passage from that final-object statement to the statement at the
object `f` of `C`, which is exactly what Remark 03P3 asserts the proof of Theorem 03P2 gives.
It has two ingredients, and neither is formal:

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
which is where `h03P2` applies.

## Main definitions

* `restrictedAssociatedPresheafIso`: `(F^a)|_D ≅ (f^*F)^a` for the presheaves of Tag 03DS.
* `restrictedAssociatedSheafIso`: the same isomorphism between the sheaves.
* `cohomologyAtObjectIso`: `H^p_τ(U, F^a) ≅ H^p(D, (f^*F)^a)` over the final object of `D`.

## Main results

* `objAtFinalObjectIso`: the object `u t` of `C` reached by the final object `t` of `D` is the
  object `f : U ⟶ S`.  This is what makes the conclusion a statement about `f`.
* `cohomologyAtFinalObjectIso`: **Remark 03P3, first assertion** — over a final object the
  `τ`-cohomology of `F^a` is the right derived functor of global sections.
* `zariskiCohomologyIsoCohomologyAtObject`: **Remark 03P3, second assertion** —
  `H^p(U, f^*F) ≅ H^p_τ(U, F^a)` at an arbitrary object `f : U ⟶ S` of the site, from
  Theorem 03P2 at the final object of the site over `U`.

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

/-- **Stacks 03P3, first assertion.**  The scheme `S` is a final object of the site `C` of
schemes over `S`, so the groups `H^p_τ(S, F^a)` on the right-hand side of Theorem 03P2 are the
right derived functors of the global sections functor of the site, that is Mathlib's global
`CategoryTheory.Sheaf.H`. -/
@[stacks 03P3 "since S is final in C, the right-hand side of 03P2 is derived global sections"]
def cohomologyAtFinalObjectIso (p : ℕ) (T : C) (hT : IsTerminal T) :
    Sheaf.H' (associatedSheaf F πC K hFa) p T ≅
      AddCommGrpCat.of (Sheaf.H (associatedSheaf F πC K hFa) p) :=
  Stacks.Cohomology.TerminalCohomology.h'IsoH K (associatedSheaf F πC K hFa) p T hT

/-- **Stacks 03P3, second assertion.**  For **any** object `f : Y ⟶ S` of the site `C` of
schemes over `S`,

`H^p(Y, f^*F) = H^p_τ(Y, F^a)`,

the left-hand side being the Zariski cohomology on `Y` of the pullback module `f^*F` and the
right-hand side the `τ`-cohomology of the associated sheaf `F^a` over the object `f` of `C`.
The object of `C` in question is `u t`, and `objAtFinalObjectIso` identifies it with
`f : Y ⟶ S`.

Theorem 03P2 is not available in this repository and is carried as the hypothesis `h03P2`, in
the form in which that theorem is stated: the comparison for the scheme `Y`, the quasi-coherent
module `f^*F` on it and the final object `t` of a site `D` of schemes over `Y`.  Everything
else is proved: `cohomologyAtObjectIso` moves the right-hand side of `h03P2` from the final
object of `D` to the object `u t` of `C`. -/
@[stacks 03P3 "H^p(U, f^*F) = H^p_tau(U, F^a) at an arbitrary object f : U ⟶ S of the site, \
with Theorem 03P2 at the final object carried as the hypothesis h03P2 and the sheaf conditions \
of 03OG as hFa and hFaPullback"]
def zariskiCohomologyIsoCohomologyAtObject (e : u ⋙ πC ≅ πD ⋙ Over.map f) (p : ℕ) (t : D)
    (h03P2 :
      Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
          ((Scheme.Modules.pullback f).obj F)) p (⊤ : Y.Opens) ≅
        Sheaf.H' (associatedSheafPullback f F πD J hFaPullback) p t) :
    Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pullback f).obj F)) p (⊤ : Y.Opens) ≅
      Sheaf.H' (associatedSheaf F πC K hFa) p (u.obj t) :=
  h03P2 ≪≫ (cohomologyAtObjectIso f F πC πD u J K hFa hFaPullback e p t).symm

end Comparison

end Stacks.EtaleCohomology.QcohSiteCohomology

end
