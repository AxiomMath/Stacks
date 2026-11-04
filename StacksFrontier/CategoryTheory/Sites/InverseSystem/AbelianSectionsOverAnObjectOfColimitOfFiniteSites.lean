module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.SectionsOverAnObjectOfColimitOfFiniteSites
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-! # The sheaf condition over an object, at abelian coefficients

`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'` is the
degree-zero step of [Stacks, Tag 09YQ] over an object `V` which neither the levels of an inverse
system of sites nor their colimit site need contain: given one finite one-hypercover datum of a
level which covers `V_n` at every level and `V` at the colimit, the sections of
`𝒢 = colim f_i^{-1}F_i` over `V` are the filtered colimit of the sections of the `F_n` over the
`V_n`. It is stated for sheaves of **sets**.

This file is its counterpart for sheaves of **abelian groups**, which is the form the geometry of
Tag 09YQ needs. The passage from an object of the colimit site to a quasi-compact open of one is
exactly what the one-hypercover step performs, and the abelian engine of [Stacks, Tag 09YP],
`Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone`, answers only over an object of
the colimit site: on a site of affine objects that is affine opens only, and the intersection of a
quasi-compact open with an affine open is a quasi-compact open of an affine scheme and need not be
affine.

## Main results

* `sectionOver_colimit_of_oneHypercoverOf_ab` — **the abelian counterpart.** Word for word the
  statement of `sectionOver_colimit_of_oneHypercoverOf'` with `Type w` replaced by `Ab.{w}`
  throughout: the same hypotheses on the system, the same two object-level inputs, the same
  one-hypercover datum at the levels and at the colimit, the same pinning of the restriction map,
  and the same conclusion.

## Implementation notes

**No "sets force abelian" device is needed, and that is not an accident of the proof.** A colimit
of abelian sheaves is not the colimit of the underlying sheaves of sets, so a statement whose
content is a universal property cannot be transported along `CategoryTheory.forget` — that is what
the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLimitColimitSheafAbelian.lean`
record for the descent along a restriction functor. The one-hypercover step is not such a
statement. Nothing in it is a colimit: the two object-level inputs `hsurjObj` and `hsep` — joint
surjectivity of the legs on sections over the objects of a level, and separatedness of the legs
there — are **hypotheses**, and everything the proof does with them is the sheaf condition over
`V` and a finite limit of sections. Both of those are statements about sections one site at a
time, and the sections of an abelian sheaf *are* the sections of the underlying sheaf of sets:
`CategoryTheory.sheafCompose` along `CategoryTheory.forget` carries an abelian sheaf to a sheaf of
sets with the same sections, because `CategoryTheory.forget Ab` is corepresentable
(`AddCommGrpCat.coyonedaObjIsoForget`), and carries the legs and the transitions to the legs and
the transitions. So the whole statement is its own set-valued instance, and the abelian structure
is not used anywhere — which is why the abelian engine may supply `hsurjObj` and `hsep` from the
*abelian* colimit presentation and still be answered here.

**The coefficients are `Ab.{w}` with `w` the universe of the objects of the sites, and that is the
exact mirror of the set-valued statement**, which is stated for sheaves of `Type w` over sites
whose objects live in `Type w`. It is also what a consumer has. The abelian presentations of
`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean` are stated
at `Ab.{max u v w t}` for a system `InverseSystemOfFiniteSites.{v, u, w}` with a free universe
`t`; at the system of sites of [Stacks, Tag 0EYL], whose index lives in `Type v` and whose site
objects live in `Type (max u v + 1)`, that is `Ab.{max (max u v + 1) t}`, and taking `t := 0`
gives exactly `Ab.{w}`.

**`ρ` is a bare function on sections, not a morphism of abelian groups.** That is weaker as a
hypothesis and so stronger as a theorem: a consumer whose restriction map is additive supplies its
underlying function, and nothing in the conclusion — joint surjectivity and separatedness — is
about the group structure.

**Every binder for a section is spelled `CategoryTheory.ToType`** rather than left to the
`CoeSort` of `Ab`, although the two are the same type. The reason is that the statement is
otherwise, as text, the set-valued one: its own binders mention only the section variables, and
`Type w` against `Ab.{w}` is invisible there, so the duplicate scan of this repository reports
this theorem as an identical restatement of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'`. It is not one —
the coefficients differ — and writing the underlying type out is what makes the difference visible
to a reader of the signature as well as to the scan.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe w u₁ u₂ v₁ v₂ v₃ v₄

namespace Stacks.WeakSites.ColimitGlobalSections

section AbelianColimitOverAnObject

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
  (Fs : ∀ i, Sheaf (D.J i) Ab.{w})
  (ψ : ∀ {i j : D.I} (a : j ⟶ i), (Fs i).obj ⟶ (D.u a).op ⋙ (Fs j).obj)
  (G : Sheaf J Ab.{w}) (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj)
  (hψ : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (Y : D.C i)
      (x : ToType ((Fs i).obj.obj (op Y))),
    (ψ (b ≫ a)).app (op Y) x =
      (Fs k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) Y).symm))
        ((ψ b).app (op ((D.u a).obj Y)) ((ψ a).app (op Y) x)))
  (hι : ∀ {i j : D.I} (a : j ⟶ i) (Y : D.C i) (x : ToType ((Fs i).obj.obj (op Y))),
    (ι i).app (op Y) x =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) ((ψ a).app (op Y) x)))
  (hsurjObj : ∀ (i : D.I) (Y : D.C i) (z : ToType (G.obj.obj (op ((u i).obj Y)))),
    ∃ (j : D.I) (a : j ⟶ i) (t : ToType ((Fs j).obj.obj (op ((D.u a).obj Y)))),
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) t) = z)
  (hsep : ∀ (i : D.I) (Y : D.C i) (j : D.I) (a : j ⟶ i)
    (t t' : ToType ((Fs j).obj.obj (op ((D.u a).obj Y)))),
    (ι j).app (op ((D.u a).obj Y)) t = (ι j).app (op ((D.u a).obj Y)) t' →
      ∃ (k : D.I) (b : k ⟶ j),
        (ψ b).app (op ((D.u a).obj Y)) t = (ψ b).app (op ((D.u a).obj Y)) t')
  {κ' ν' : Type} (i₀ : D.I) (W₀ : κ' → D.C i₀) (P₀ : κ' → κ' → ν' → D.C i₀)
  (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l)
  {A₀ : Type v₁} [Category.{v₂} A₀] {K₀ : GrothendieckTopology A₀} (w₀ : C ⥤ A₀)
  (G' : Sheaf K₀ Ab.{w}) (e₀ : w₀.op ⋙ G'.obj ≅ G.obj)
  {V : A₀} {fV : ∀ k, w₀.obj ((u i₀).obj (W₀ k)) ⟶ V}
  (hV : IsOneHypercoverOf K₀ V (fun k => w₀.obj ((u i₀).obj (W₀ k))) fV
    (fun k l m => w₀.obj ((u i₀).obj (P₀ k l m)))
    (fun k l m => w₀.map ((u i₀).map (q₁ k l m)))
    (fun k l m => w₀.map ((u i₀).map (q₂ k l m))))
  {A : D.I → Type v₃} [∀ n, Category.{v₄} (A n)] {K : ∀ n, GrothendieckTopology (A n)}
  (wn : ∀ n, D.C n ⥤ A n) (Hs : ∀ n, Sheaf (K n) Ab.{w})
  (en : ∀ n, (wn n).op ⋙ (Hs n).obj ≅ (Fs n).obj)
  {Vn : ∀ {n : D.I}, (n ⟶ i₀) → A n}
  {fVn : ∀ {n : D.I} (a : n ⟶ i₀) (k : κ'), (wn n).obj ((D.u a).obj (W₀ k)) ⟶ Vn a}
  (hVn : ∀ {n : D.I} (a : n ⟶ i₀), IsOneHypercoverOf (K n) (Vn a)
    (fun k => (wn n).obj ((D.u a).obj (W₀ k))) (fVn a)
    (fun k l m => (wn n).obj ((D.u a).obj (P₀ k l m)))
    (fun k l m => (wn n).map ((D.u a).map (q₁ k l m)))
    (fun k l m => (wn n).map ((D.u a).map (q₂ k l m))))

include hu hψ hι hsurjObj hsep hV hVn in
/-- **(★) at abelian coefficients: Stacks 09YQ in degree zero, for sheaves of abelian groups, over
an object neither the levels nor the colimit site need contain.** Let `(C i, J i)` be an inverse
system of sites with finite coverings, let `F_i` be a system of **abelian** sheaves on it and let
`𝒢 = colim f_i^{-1}F_i` be an abelian sheaf on the colimit site, with legs `ι_i` compatible with
the transitions `ψ`. Assume the two object-level inputs: every section of `𝒢` over the image of an
object of a level comes from a section of some level below (`hsurjObj`), and two sections of a
level with the same image in `𝒢` agree at a further level (`hsep`). Let `V` be an object of an
ambient site of the colimit, let `V_n` be objects of ambient sites of the levels, and let a single
finite datum `(W₀, P₀, q₁, q₂)` of objects of the level `i₀` be — in its image at each level and at
the colimit — a one-hypercover of `V_n` and of `V` respectively. Then the sections of `𝒢` over `V`
are the filtered colimit of the sections of the `F_n` over the `V_n`: every section of `𝒢` over
`V` is the image of a section of some `F_n` over `V_n`, and two sections of `F_n` over `V_n` with
the same image agree, on the objects of the datum, at a further level.

This is `Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'` with
`Type w` replaced by `Ab.{w}`, and it is that theorem's own instance at the underlying sheaves of
sets. Composition with `CategoryTheory.forget Ab` carries an abelian sheaf to a sheaf of sets
(`CategoryTheory.sheafCompose`, available because `CategoryTheory.forget Ab` is corepresentable),
and it carries the sections, the transitions `ψ`, the legs `ι`, the restriction isomorphisms `e₀`
and `en` and the pinning `hρ` to themselves: the sections of an abelian sheaf over an object are
the sections of its underlying sheaf of sets over that object, definitionally, and each hypothesis
above is already a statement about those. The module's implementation notes record why no
transport of a universal property — no "sets force abelian" device — is needed or possible:
nothing in this statement is a colimit, the two colimit inputs being hypotheses. -/
theorem sectionOver_colimit_of_oneHypercoverOf_ab [Finite κ'] [Finite ν']
    (ρ : ∀ (n : D.I) (a : n ⟶ i₀),
      ToType ((Hs n).obj.obj (op (Vn a))) → ToType (G'.obj.obj (op V)))
    (hρ : ∀ (n : D.I) (a : n ⟶ i₀) (t : ToType ((Hs n).obj.obj (op (Vn a)))) (k : κ'),
      e₀.hom.app (op ((u i₀).obj (W₀ k))) (G'.obj.map (fV k).op (ρ n a t)) =
        G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) (W₀ k))))
          ((ι n).app (op ((D.u a).obj (W₀ k)))
            ((en n).hom.app (op ((D.u a).obj (W₀ k)))
              ((Hs n).obj.map (fVn a k).op t)))) :
    (∀ s : ToType (G'.obj.obj (op V)),
        ∃ (n : D.I) (a : n ⟶ i₀) (t : ToType ((Hs n).obj.obj (op (Vn a)))), ρ n a t = s) ∧
      ∀ (n : D.I) (a : n ⟶ i₀) (t t' : ToType ((Hs n).obj.obj (op (Vn a)))),
        ρ n a t = ρ n a t' →
        ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
          (ψ b).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t)) =
            (ψ b).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t')) :=
  sectionOver_colimit_of_oneHypercoverOf' D u hu
    (fun i => (sheafCompose (D.J i) (forget Ab.{w})).obj (Fs i))
    (fun {_ _} a => Functor.whiskerRight (ψ a) (forget Ab.{w}))
    ((sheafCompose J (forget Ab.{w})).obj G)
    (fun i => Functor.whiskerRight (ι i) (forget Ab.{w}))
    hψ hι hsurjObj hsep i₀ W₀ P₀ q₁ q₂ w₀
    ((sheafCompose K₀ (forget Ab.{w})).obj G')
    (Functor.isoWhiskerRight e₀ (forget Ab.{w})) hV wn
    (fun n => (sheafCompose (K n) (forget Ab.{w})).obj (Hs n))
    (fun n => Functor.isoWhiskerRight (en n) (forget Ab.{w})) hVn ρ hρ

end AbelianColimitOverAnObject

end Stacks.WeakSites.ColimitGlobalSections

end
